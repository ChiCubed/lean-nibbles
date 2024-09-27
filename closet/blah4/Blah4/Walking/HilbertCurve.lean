import Mathlib

open unitInterval

namespace unitInterval

@[simps]
noncomputable def half : I := ⟨2⁻¹, Set.mem_Icc.mpr <| by norm_num⟩

@[simps]
noncomputable def path (a b : I) : Path a b where
  toFun t := ⟨a + t * (b - a), by
    rcases a with ⟨a, ha₀, ha₁⟩
    rcases b with ⟨b, hb₀, hb₁⟩
    rcases t with ⟨t, ht₀, ht₁⟩
    rw [Set.mem_Icc]
    constructor <;> nlinarith⟩
  source' := by simp
  target' := by simp

@[simps]
noncomputable def leftHalf : C(I, I) where
  toFun x := ⟨x / 2, by
    rcases x with ⟨x, hx₀, hx₁⟩
    rw [Set.mem_Icc]
    constructor <;> linarith⟩

@[simps]
noncomputable def rightHalf : C(I, I) where
  toFun x := ⟨(1 + x) / 2, by
    rcases x with ⟨x, hx₀, hx₁⟩
    rw [Set.mem_Icc]
    constructor <;> linarith⟩

@[simps]
def symmMap : C(I, I) where
  toFun x := symm x

@[simp] theorem path01_apply t :
  path01 t = t := rfl

@[simp] theorem dist_le_one (a b : I) : dist a b ≤ 1 := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  rcases a with ⟨a, ha₀, ha₁⟩
  rcases b with ⟨b, hb₀, hb₁⟩
  constructor <;> linarith

end unitInterval


namespace ContinuousMap

def unprod {α β₁ β₂ : Type*} [TopologicalSpace α] [TopologicalSpace β₁] [TopologicalSpace β₂]
    (f : C(α, β₁ × β₂)) : (fx : C(α, β₁)) × (fy : C(α, β₂)) ×' f = fx.prodMk fy :=
  ⟨fst.comp f, snd.comp f, by ext <;> simp⟩

theorem dist_eq_iSup {α β} [TopologicalSpace α] [CompactSpace α] [MetricSpace β]
  {f g : C(α, β)} :
    dist f g = ⨆ x, dist (f x) (g x) := by
  convert BoundedContinuousFunction.dist_eq_iSup using 0

namespace Homotopy

@[simp] theorem trans_leftHalf_apply {X Y}
  [TopologicalSpace X] [TopologicalSpace Y] {f g h : C(X, Y)}
  (a : ContinuousMap.Homotopy f g) (b : ContinuousMap.Homotopy g h) {t x} :
    (a.trans b) (leftHalf t, x) = a (t, x) := by
  simp only [trans_apply, leftHalf, coe_mk,
    show (t / 2 : ℝ) ≤ 1 / 2 by linarith [t.2.2], ↓reduceDite]
  congr
  linarith

@[simp] theorem trans_rightHalf_apply {X Y}
  [TopologicalSpace X] [TopologicalSpace Y] {f g h : C(X, Y)}
  (a : ContinuousMap.Homotopy f g) (b : ContinuousMap.Homotopy g h) {t x} :
    (a.trans b) (rightHalf t, x) = b (t, x) := by
  simp only [trans_apply, rightHalf, coe_mk]
  obtain rfl | ht : t = 0 ∨ 0 < (t : ℝ) := eq_or_gt_of_le t.2.1
  . simp only [Set.Icc.coe_zero, add_zero, le_refl, ↓reduceDite]
    norm_num1
    simp only [Set.Icc.mk_one, apply_one, apply_zero]
  simp only [show ¬ ((1 + t) / 2 : ℝ) ≤ 1 / 2 by linarith [ht], ↓reduceDite]
  congr
  linarith

@[simp] theorem dist_trans {X Y}
  [TopologicalSpace X] [CompactSpace X] [MetricSpace Y] {f₁ f₂ g₁ g₂ h₁ h₂ : C(X, Y)}
  (a₁ : ContinuousMap.Homotopy f₁ g₁) (a₂ : ContinuousMap.Homotopy f₂ g₂)
  (b₁ : ContinuousMap.Homotopy g₁ h₁) (b₂ : ContinuousMap.Homotopy g₂ h₂) :
    dist (α := C(I × X, Y)) (a₁.trans b₁) (a₂.trans b₂) =
    max
      (dist (α := C(I × X, Y)) a₁ a₂)
      (dist (α := C(I × X, Y)) b₁ b₂) := by
  obtain hX | hX := isEmpty_or_nonempty X
  . convert Eq.symm <| max_self (0 : ℝ) <;> rw [dist_eq_zero] <;> ext x <;> exact hX.elim x.2
  simp_rw [dist_eq_iSup, ContinuousMap.coe_coe]
  have hd {f g : C(I × X, Y)} : BddAbove (Set.range fun x => dist (f x) (g x))
  . rw [← Set.image_univ]
    apply IsCompact.bddAbove_image isCompact_univ
    rw [← continuous_iff_continuousOn_univ]
    continuity
  apply le_antisymm
  . apply ciSup_le
    rintro ⟨t, x⟩
    simp_rw [trans_apply]
    dsimp only
    split <;> [ apply le_max_of_le_left; apply le_max_of_le_right ] <;> apply le_ciSup hd
  . apply max_le <;>
      apply ciSup_le <;>
      rintro ⟨t, x⟩ <;>
      [ apply le_ciSup_of_le hd (leftHalf t, x);
        apply le_ciSup_of_le hd (rightHalf t, x) ]
    all_goals
    . simp only [coe_toContinuousMap, trans_leftHalf_apply, trans_rightHalf_apply]
      rfl

theorem refl_trans_refl {X Y}
  [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} :
    trans (refl f) (refl f) = refl f := by
  ext; simp [trans_apply]

end Homotopy

end ContinuousMap


namespace HilbertCurve

noncomputable section Aux

private def p (n : ℕ) : I :=
  ⟨2 ^ (-n - 1 : ℤ), by
    rw [Set.mem_Icc]
    constructor
    . positivity
    . apply zpow_le_one_of_nonpos <;> linarith⟩

@[simp]
private theorem p_zero : (p 0 : ℝ) = 2⁻¹ := by
  simp [p]

@[simp]
private theorem p_succ (n : ℕ) : (p (n+1) : ℝ) = (p n : ℝ) / 2 := by
  unfold p
  push_cast
  rw [neg_add_rev, add_sub_assoc, zpow_add₀]
  . ring
  . norm_num

@[simp]
private theorem p_pos {n} : 0 < (p n : ℝ) := by
  dsimp [p]
  positivity

@[simp]
private theorem p_le_half {n} : (p n : ℝ) ≤ 1 / 2 := by
  dsimp [p]
  rw [show (1 / 2 : ℝ) = 2 ^ (-1 : ℤ) by norm_num]
  gcongr <;> simp

-- the unit square is in ℝ^2, obviously
-- (TODO: do i want ext theorems accompanying this?)
def squareCoe (x : I × I) : ℝ × ℝ := (x.1, x.2)

local instance : CoeOut (I × I) (ℝ × ℝ) where
  coe := squareCoe

@[simp] theorem squareCoe_mk (x y : I) : (((x, y) : I × I) : ℝ × ℝ) = (↑x, ↑y) := rfl

@[simp] theorem squareCoe_inj {a b : I × I} : (a : ℝ × ℝ) = b ↔ a = b := by aesop

def aux.base_l : Path (X := I × I) (p 0, 0) (1, p 0) :=
  .trans
    (Path.prod (.refl (p 0)) (path01.map <| map_continuous leftHalf) |>.cast
      (by ext <;> simp)
      (rfl))
    (Path.prod (path01.map <| map_continuous rightHalf) (.refl (p 0)) |>.cast
      (by ext <;> simp)
      (by ext <;> simp))

def aux.base_i : Path (X := I × I) (0, p 0) (1, p 0) :=
  .prod path01 (.refl _)

-- (most of) the self-similarities
def aux.q : Fin 4 → C(I × I, I × I) :=
  let q0 := leftHalf.prodMap leftHalf |>.comp .prodSwap
  let q1 := leftHalf.prodMap rightHalf
  let symm_x := symmMap.prodMap (.id I)
  ![q0, q1, symm_x.comp q1, symm_x.comp q0]

theorem aux.q0_def : q 0 = (leftHalf.prodMap leftHalf |>.comp .prodSwap) := rfl
theorem aux.q1_def : q 1 = (leftHalf.prodMap rightHalf) := rfl
theorem aux.q2_def : q 2 = (symmMap.prodMap (.id I) |>.comp <| leftHalf.prodMap rightHalf) := rfl
theorem aux.q3_def : q 3 = (symmMap.prodMap (.id I) |>.comp <| leftHalf.prodMap leftHalf |>.comp .prodSwap) := rfl

-- TODO:
-- register a simp extension for these guys?
@[simp] theorem aux.q0_x p : (q 0 p).1 = (p.2 / 2 : ℝ) := by simp [q0_def]
@[simp] theorem aux.q0_y p : (q 0 p).2 = (p.1 / 2 : ℝ) := by simp [q0_def]
@[simp] theorem aux.q1_x p : (q 1 p).1 = (p.1 / 2 : ℝ) := by simp [q1_def]
@[simp] theorem aux.q1_y p : (q 1 p).2 = ((1 + p.2) / 2 : ℝ) := by simp [q1_def]
@[simp] theorem aux.q2_x p : (q 2 p).1 = (1 - p.1 / 2 : ℝ) := by simp [q2_def]
@[simp] theorem aux.q2_y p : (q 2 p).2 = ((1 + p.2) / 2 : ℝ) := by simp [q2_def]
@[simp] theorem aux.q3_x p : (q 3 p).1 = (1 - p.2 / 2 : ℝ) := by simp [q3_def]
@[simp] theorem aux.q3_y p : (q 3 p).2 = (p.1 / 2 : ℝ) := by simp [q3_def]
-- @[simp] theorem aux.q0_apply p : (q 0 p : ℝ × ℝ) = ((p.2 / 2 : ℝ), (p.1 / 2 : ℝ)) := by simp [q0_def]
-- @[simp] theorem aux.q1_apply p : (q 1 p : ℝ × ℝ) = ((p.1 / 2 : ℝ), ((1 + p.2) / 2 : ℝ)) := by simp [q1_def]
-- @[simp] theorem aux.q2_apply p : (q 2 p : ℝ × ℝ) = ((1 - p.1 / 2 : ℝ), ((1 + p.2) / 2 : ℝ)) := by simp [q2_def]
-- @[simp] theorem aux.q3_apply p : (q 3 p : ℝ × ℝ) = ((1 - p.2 / 2 : ℝ), (p.1 / 2 : ℝ)) := by simp [q3_def]
-- @[simp] theorem aux.q0_x p : (q 0 p).1 = (p.2 / 2 : ℝ) := by simp [← squareCoe_inj, q0_apply]
-- @[simp] theorem aux.q0_y p : (q 0 p : ℝ × ℝ) = ((p.2 / 2 : ℝ), (p.1 / 2 : ℝ)) := by simp [q0_def]
-- @[simp] theorem aux.q1_x p : (q 1 p : ℝ × ℝ) = ((p.1 / 2 : ℝ), ((1 + p.2) / 2 : ℝ)) := by simp [q1_def]
-- @[simp] theorem aux.q1_y p : (q 1 p : ℝ × ℝ) = ((p.1 / 2 : ℝ), ((1 + p.2) / 2 : ℝ)) := by simp [q1_def]
-- @[simp] theorem aux.q2_x p : (q 2 p : ℝ × ℝ) = ((1 - p.1 / 2 : ℝ), ((1 + p.2) / 2 : ℝ)) := by simp [q2_def]
-- @[simp] theorem aux.q2_y p : (q 2 p : ℝ × ℝ) = ((1 - p.1 / 2 : ℝ), ((1 + p.2) / 2 : ℝ)) := by simp [q2_def]
-- @[simp] theorem aux.q3_x p : (q 3 p : ℝ × ℝ) = ((1 - p.2 / 2 : ℝ), (p.1 / 2 : ℝ)) := by simp [q3_def]
-- @[simp] theorem aux.q3_y p : (q 3 p : ℝ × ℝ) = ((1 - p.2 / 2 : ℝ), (p.1 / 2 : ℝ)) := by simp [q3_def]

-- NOTE: the distance here is actually chebyshev!
@[simp] theorem aux.q_dist_map {i} a b : dist (q i a) (q i b) = dist a b / 2 := by
  fin_cases i
  all_goals
  . push_cast
    simp only [Prod.dist_eq, Subtype.dist_eq, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
      leftHalf, rightHalf, unitInterval.symm, ContinuousMap.coe_mk,
      add_div, dist_add_left, dist_sub_left, Real.dist_eq, ← sub_div, abs_div, abs_two,
      max_div_div_right (show 0 ≤ (2 : ℝ) by norm_num), max_comm]

@[simp] theorem aux.q_inj {i} a b : q i a = q i b ↔ a = b := by
  rw [← dist_eq_zero (x := q i a), ← dist_eq_zero (x := a)]
  simp

@[simp]
def aux.autoCast {X} [TopologicalSpace X]
    {x y : X} (γ : Path x y) {x' y' : X}
    (hx : x' = x := by ext <;> simp <;> norm_num) (hy : y' = y := by ext <;> simp <;> norm_num) : Path x' y' :=
  γ.cast hx hy

-- returns a "L-shaped" and "I-shaped"
-- n-th step of Hilbert curve construction.
-- they barely differ, so this feels a bit silly,
-- but whatever.
open aux in
def aux : (n : ℕ) →
  Path (X := I × I) (p n, 0) (1, p n) ×
  Path (X := I × I) (0, p n) (1, p n)
| 0 => (aux.base_l, aux.base_i)
| n+1 =>
  let (l, i) := aux n
  let p0_l : Path (p (n+1), 0) _ := autoCast <| i.map <| map_continuous <| q 0
  let p0_i : Path (0, p (n+1)) _ := autoCast <| l.map <| map_continuous <| q 0
  let p1 : Path (p (n+1), p 0) _ := autoCast <| l.map <| map_continuous <| q 1
  let p2 : Path (p 0, rightHalf (p n)) _ := autoCast <| .symm <| l.map <| map_continuous <| q 2
  let p3 : Path (σ (p (n+1)), p 0) _ := autoCast <| .symm <| l.map <| map_continuous <| q 3
  ((p0_l.trans p1).trans (p2.trans p3),
   (p0_i.trans p1).trans (p2.trans p3))


open Path in
@[simp]
theorem aux.zero_l_apply t :
  (aux 0).1 t =
    if (t : ℝ) ≤ 1/2 then
      (p 0, t)
    else
      (t, p 0) := by
  simp only [aux, base_l, trans_apply, cast_coe, prod_coe,
    refl_apply, map_coe, Function.comp_apply]
  split_ifs <;> simp [leftHalf, rightHalf, mul_div_cancel_left]

@[simp]
theorem aux.zero_i_apply t :
  (aux 0).2 t =
    (t, p 0) := by
  simp [aux, base_i]

def aux.t0 (t : I)
    (t_hi : (t : ℝ) ≤ 1/4 := by assumption) : I :=
  ⟨4*t, Set.mem_Icc.mpr <| by constructor <;> linarith only [t.2.1, show _ ≤ _ from t_hi]⟩

def aux.t1 (t : I)
    (t_lo : ¬ (t : ℝ) ≤ 1/4 := by assumption) (t_hi : (t : ℝ) ≤ 2/4 := by assumption) : I :=
  ⟨4*t - 1, Set.mem_Icc.mpr <| by constructor <;> linarith only [show ¬ _ ≤ _ from t_lo, show _ ≤ _ from t_hi]⟩

def aux.t2 (t : I)
    (t_lo : ¬ (t : ℝ) ≤ 2/4 := by assumption) (t_hi : (t : ℝ) ≤ 3/4 := by assumption) : I :=
  ⟨3 - 4*t, Set.mem_Icc.mpr <| by constructor <;> linarith only [show ¬ _ ≤ _ from t_lo, show _ ≤ _ from t_hi]⟩

def aux.t3 (t : I)
    (t_lo : ¬ (t : ℝ) ≤ 3/4 := by assumption) : I :=
  ⟨4 - 4*t, Set.mem_Icc.mpr <| by constructor <;> linarith only [show ¬ _ ≤ _ from t_lo, t.2.2]⟩

@[simp] theorem aux.t0_inj a b {ha hb} : t0 a ha = t0 b hb ↔ a = b := by simp [t0, Subtype.coe_inj]
@[simp] theorem aux.t1_inj a b {ha₁ ha₂ hb₁ hb₂} : t1 a ha₁ ha₂ = t1 b hb₁ hb₂ ↔ a = b := by simp [t1, Subtype.coe_inj]
@[simp] theorem aux.t2_inj a b {ha₁ ha₂ hb₁ hb₂} : t2 a ha₁ ha₂ = t2 b hb₁ hb₂ ↔ a = b := by simp [t2, Subtype.coe_inj]
@[simp] theorem aux.t3_inj a b {ha hb} : t3 a ha = t3 b hb ↔ a = b := by simp [t3, Subtype.coe_inj]

-- @[simp] theorem aux.t0_eq_zero a {h} : t0 a h = 0 ↔ (a : ℝ) = 0 := by
--   convert t0_inj a (t0 0 (by norm_num)) <;> norm_num
-- @[simp] theorem aux.t0_eq_one a {h} : t0 a h = 1 ↔ (a : ℝ) = 1/4 := by
--   convert t0_inj a ⟨1/4, by norm_num⟩ <;> simp [← Subtype.coe_inj]
@[simp] theorem aux.t1_ne_zero a {h₁ h₂} : ¬ t1 a h₁ h₂ = 0 := by
  rw [← Subtype.coe_inj]; simp only [t1]; push_cast; linarith
-- @[simp] theorem aux.t1_eq_one a {h₁ h₂} : t1 a h₁ h₂ = 1 ↔ (a : ℝ) = 2/4 := by
--   convert t1_inj a ⟨2/4, by norm_num⟩ <;> simp only [t1, ← Subtype.coe_inj] <;> norm_num
-- @[simp] theorem aux.t2_eq_zero a {h₁ h₂} : t2 a h₁ h₂ = 0 ↔ (a : ℝ) = 3/4 := by
--   convert t2_inj a ⟨3/4, by norm_num⟩ <;> simp only [t2, ← Subtype.coe_inj] <;> norm_num
@[simp] theorem aux.t2_ne_one a {h₁ h₂} : ¬ t2 a h₁ h₂ = 1 := by
  rw [← Subtype.coe_inj]; simp only [t2]; push_cast; linarith
-- @[simp] theorem aux.t3_eq_zero a {h} : t3 a h = 0 ↔ (a : ℝ) = 1 := by
--   convert t3_inj a ⟨1, by norm_num⟩ <;> norm_num
@[simp] theorem aux.t3_ne_one a {h} : ¬ t3 a h = 1 := by
  rw [← Subtype.coe_inj]; simp only [t3]; push_cast; linarith

@[simp]
theorem aux.succ_l_apply n t :
  (aux (n+1)).1 t =
    if h₁ : (t : ℝ) ≤ 1/4 then
      q 0 <| (aux n).2 <| t0 t
    else if h₂ : (t : ℝ) ≤ 2/4 then
      q 1 <| (aux n).1 <| t1 t
    else if h₃ : (t : ℝ) ≤ 3/4 then
      q 2 <| (aux n).1 <| t2 t
    else
      q 3 <| (aux n).1 <| t3 t := by
  rcases t with ⟨t, ht₀, ht₁⟩
  simp only [aux, Path.trans_apply]
    -- show 2 * t ≤ 1 / 2 ↔ t ≤ 1 / 4 by constructor <;> intro <;> linarith,
    -- show t ≤ 1 / 2 ↔ t ≤ 2 / 4 by norm_num,
    -- show 2 * t - 1 ≤ 1 / 2 ↔ t ≤ 3 / 4 by constructor <;> intro <;> linarith]
  split_ifs <;> first
  | exfalso; linarith
  | simp only [Nat.add_eq, Nat.add_zero, unitInterval.symm, autoCast, Path.map_symm, Path.cast_coe,
      Path.map_coe, Fin.isValue, Function.comp_apply, Path.symm_apply, t0, t1, t2, t3]
    congr 3
    linarith
  -- or just manually walk the tree:
  -- split_ifs h₁ h₂ h₃ <;> dsimp only at * <;> simp only [aux]
  -- . rw [Path.trans_apply, dite_cond_eq_true (eq_true <| by dsimp; linarith),
  --     Path.trans_apply, dite_cond_eq_true (eq_true <| by dsimp; linarith)]
  --   simp [show 2 * (2 * t) = 4 * t by linarith]
  -- . rw [Path.trans_apply, dite_cond_eq_true (eq_true <| by dsimp; linarith),
  --     Path.trans_apply, dite_cond_eq_false (eq_false <| by dsimp; linarith)]
  --   simp [show 2 * (2 * t) - 1 = 4 * t - 1 by linarith]
  -- . rw [Path.trans_apply, dite_cond_eq_false (eq_false <| by dsimp; linarith),
  --     Path.trans_apply, dite_cond_eq_true (eq_true <| by dsimp; linarith)]
  --   simp [unitInterval.symm, show 1 - 2 * (2 * t - 1) = 3 - 4 * t by linarith]
  -- . rw [Path.trans_apply, dite_cond_eq_false (eq_false <| by dsimp; linarith),
  --     Path.trans_apply, dite_cond_eq_false (eq_false <| by dsimp; linarith)]
  --   simp [unitInterval.symm, show 1 - (2 * (2 * t - 1) - 1) = 4 - 4 * t by linarith]

lemma aux.succ_shared_apply n {t : I} (ht : 1/4 < (t : ℝ)) :
    (aux (n+1)).1 t = (aux (n+1)).2 t := by
  simp only [aux]
  simp_rw [Path.trans_apply (t := t)]
  rcases t with ⟨t, ht₀, ht₁⟩
  split_ifs with h <;> dsimp only at *
  simp_rw [Path.trans_apply]
  repeat rw [dite_cond_eq_false (eq_false <| by linarith)]

@[simp]
theorem aux.succ_i_apply n t :
  (aux (n+1)).2 t =
    if h₁ : (t : ℝ) ≤ 1/4 then
      q 0 <| (aux n).1 <| t0 t
    else if h₂ : (t : ℝ) ≤ 2/4 then
      q 1 <| (aux n).1 <| t1 t
    else if h₃ : (t : ℝ) ≤ 3/4 then
      q 2 <| (aux n).1 <| t2 t
    else
      q 3 <| (aux n).1 <| t3 t := by
  rcases t with ⟨t, ht₀, ht₁⟩
  split <;> rename_i h <;> try dsimp only at *
  . simp only [aux]
    rw [Path.trans_apply, dite_cond_eq_true (eq_true <| by dsimp; linarith),
      Path.trans_apply, dite_cond_eq_true (eq_true <| by dsimp; linarith)]
    simp [t0, t1, t2, t3, show 2 * (2 * t) = 4 * t by linarith]
  . repeat rw [← aux.succ_shared_apply n (by dsimp; linarith), aux.succ_l_apply]
    split <;> rename_i h'
    . contradiction
    . rfl

private def line (a b : I × I) : Path a b :=
  (path a.1 b.1).prod (path a.2 b.2)

@[simp]
theorem line_def {a b} t :
    (line a b t : ℝ × ℝ) = ↑a + (t : ℝ) • (↑b - ↑a) :=
  rfl

@[simp]
theorem line_def_x {a b} t :
    (line a b t |>.1 : ℝ) = a.1 + t * (b.1 - a.1) :=
  rfl

@[simp]
theorem line_def_y {a b} t :
    (line a b t |>.2 : ℝ) = a.2 + t * (b.2 - a.2) :=
  rfl

-- TODO:
-- this line and linearHomotopy stuff really wants a rework.

@[simps]
private def linearHomotopy (f₀ f₁ : C(I, I × I)) :
    ContinuousMap.Homotopy f₀ f₁ where
  toFun := fun | (t, x) => line (f₀ x) (f₁ x) t
  continuous_toFun := by
    obtain ⟨f₀x, f₀y, rfl⟩ := f₀.unprod
    obtain ⟨f₁x, f₁y, rfl⟩ := f₁.unprod
    unfold line
    continuity
  map_zero_left x := by simp
  map_one_left x := by simp

def aux.homotopy_l n := linearHomotopy (aux n).1 (aux (n+1)).1
def aux.homotopy_i n := linearHomotopy (aux n).2 (aux (n+1)).2

def squareBoundary : Set (I × I) := ({0, 1} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {0, 1})
@[simp] theorem mem_squareBoundary x y :
    (x, y) ∈ squareBoundary ↔ x = 0 ∨ x = 1 ∨ y = 0 ∨ y = 1 := by
  simp [squareBoundary, or_assoc]

theorem not_mem_squareBoundary x y :
    (x, y) ∉ squareBoundary ↔ 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 := by
  rw [mem_squareBoundary]
  simp_rw [not_or, ← Subtype.coe_inj]
  congr!
  . exact x.2.1.gt_iff_ne.symm
  . exact x.2.2.lt_iff_ne.symm
  . exact y.2.1.gt_iff_ne.symm
  . exact y.2.2.lt_iff_ne.symm

lemma aux.q_mem_squareBoundary {n x} (hx : q n x ∈ squareBoundary) :
    x ∈ squareBoundary := by
  fin_cases n <;>
  . push_cast at hx
    rw [mem_squareBoundary] at hx
    simp only [← Subtype.coe_inj] at hx
    simp only [q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y] at hx
    rcases x with ⟨⟨x, hx₀, hx₁⟩, ⟨y, hy₀, hy₁⟩⟩
    contrapose! hx
    rw [not_mem_squareBoundary] at hx
    simp only [← Subtype.coe_lt_coe] at hx
    push_cast at hx ⊢
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma aux.line_mem_squareBoundary {x y} {t} (h : line x y t ∈ squareBoundary) :
    x ∈ squareBoundary ∨ y ∈ squareBoundary := by
  contrapose! h
  obtain rfl | ht₀ : t = 0 ∨ 0 < (t : ℝ) := by
    rw [← Subtype.coe_inj]
    exact t.2.1.eq_or_gt
  . simp only [Path.source, h.1]; trivial
  obtain rfl | ht₁ : t = 1 ∨ (t : ℝ) < 1 := by
    rw [← Subtype.coe_inj]
    exact t.2.2.eq_or_lt
  . simp only [Path.target, h.2]; trivial
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp_rw [not_mem_squareBoundary] at h
  rw [not_mem_squareBoundary]
  simp_rw [← Subtype.coe_lt_coe, line_def_x, line_def_y] at h ⊢
  push_cast at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma aux.boundary n :
    (∀ x, (aux n).1 x ∈ squareBoundary → x = 0 ∨ x = 1) ∧
    (∀ x, (aux n).2 x ∈ squareBoundary → x = 0 ∨ x = 1) := by
  induction n with
  | zero =>
    constructor <;>
      intro x <;>
      simp only [zero_l_apply, zero_i_apply] <;>
      [ split; skip ] <;>
      simp only [mem_squareBoundary, ← Subtype.coe_inj, p_zero] <;>
      norm_num
  | succ n ih =>
    rcases ih with ⟨ih_l, ih_i⟩
    constructor <;>
    . intro x
      simp only [succ_l_apply, succ_i_apply]
      split_ifs <;>
      . intro h
        have h' := q_mem_squareBoundary h
        first | apply ih_l at h' | apply ih_i at h'
        rcases h' with h' | h'
        all_goals first
        | simp only [t0, t1, t2, t3, ← Subtype.coe_inj] at h' ⊢
          push_cast at h' ⊢
          first | left; linarith only [h'] | right; linarith only [h']
        | simp only [h', Path.source, Path.target] at h
          rw [mem_squareBoundary] at h
          simp only [← Subtype.coe_inj, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y] at h
          push_cast at h
          contrapose! h
          refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [p_pos (n := n), p_le_half (n := n)]


theorem aux.l_boundary n {x} :
    (aux n).1 x ∈ squareBoundary ↔ x = 0 ∨ x = 1 :=
  ⟨aux.boundary n |>.1 x, by rintro (rfl | rfl) <;> simp⟩

theorem aux.i_boundary n {x} :
    (aux n).2 x ∈ squareBoundary ↔ x = 0 ∨ x = 1 :=
  ⟨aux.boundary n |>.2 x, by rintro (rfl | rfl) <;> simp⟩

theorem aux.homotopy_l_boundary n t ⦃x⦄ :
    homotopy_l n (t, x) ∈ squareBoundary ↔ x = 0 ∨ x = 1 := by
  constructor
  . intro h
    simp only [homotopy_l, linearHomotopy_apply, ContinuousMap.coe_coe] at h
    apply line_mem_squareBoundary at h
    exact h.elim (l_boundary _).mp (l_boundary _).mp
  . rintro (rfl | rfl) <;>
    . simp only [homotopy_l, linearHomotopy_apply, ContinuousMap.coe_coe]
      first | rw [Path.source, Path.source] | rw [Path.target, Path.target]
      rw [mem_squareBoundary]
      simp only [← Subtype.coe_inj, line_def_x, line_def_y]
      norm_num

theorem aux.homotopy_i_boundary n t ⦃x⦄ :
    homotopy_i n (t, x) ∈ squareBoundary ↔ x = 0 ∨ x = 1 := by
  constructor
  . intro h
    simp only [homotopy_i, linearHomotopy_apply, ContinuousMap.coe_coe] at h
    apply line_mem_squareBoundary at h
    exact h.elim (i_boundary _).mp (i_boundary _).mp
  . rintro (rfl | rfl) <;>
    . simp only [homotopy_i, linearHomotopy_apply, ContinuousMap.coe_coe]
      first | rw [Path.source, Path.source] | rw [Path.target, Path.target]
      rw [mem_squareBoundary]
      simp only [← Subtype.coe_inj, line_def_x, line_def_y]
      norm_num

theorem aux.q_inter {i j} (hij : i ≠ j) {a b} (h : q i a = q j b) :
    a ∈ squareBoundary ∧ b ∈ squareBoundary := by
  wlog hlt : i < j
  . exact .symm <| this hij.symm h.symm <| (le_of_not_lt hlt).lt_of_ne hij.symm
  fin_cases i <;> fin_cases j <;> push_cast at * <;> clear hij hlt
  all_goals
  . rw [Prod.mk.injEq] at h
    simp only [← Subtype.coe_inj, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y] at h
    by_contra hc
    rw [not_and_or] at hc
    rcases a with ⟨⟨a1, ha1₁, ha1₂⟩, ⟨a2, ha2₁, ha2₂⟩⟩
    rcases b with ⟨⟨b1, hb1₁, hb1₂⟩, ⟨b2, hb2₁, hb2₂⟩⟩
    dsimp only at h
    rcases hc with hc | hc <;> rw [not_mem_squareBoundary] at hc <;>
      simp_rw [← Subtype.coe_lt_coe] at hc <;> push_cast at hc <;>
      linarith (config := { splitHypotheses := true })


theorem linearHomotopy_timewise_injective_iff f g :
    (∀ t, Function.Injective (linearHomotopy f g |>.curry t)) ↔
    (∀ ⦃x y⦄, x < y → 0 ∉ segment ℝ (f y - f x : ℝ × ℝ) (g y - g x : ℝ × ℝ)) := by
  simp_rw [mem_segment_iff_wbtw.not]
  have this x y t :
      (linearHomotopy f g).curry t x = (linearHomotopy f g).curry t y ↔
      AffineMap.lineMap (f y - f x : ℝ × ℝ) (g y - g x : ℝ × ℝ) (t : ℝ) = 0
  . simp only [ContinuousMap.Homotopy.curry_apply, linearHomotopy]
    change line (f x) (g x) t = line (f y) (g y) t ↔ _
    simp only [← squareCoe_inj, line_def]
    simp_rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_add, smul_sub]
    rw [← sub_eq_zero, ← neg_eq_zero]
    ring_nf
  constructor
  case mp =>
    rintro h x y hxy ⟨t, t_prop, ht⟩
    lift t to I using t_prop
    absurd h t |>.ne hxy.ne
    rwa [this]
  case mpr =>
    intro h t x y hc
    wlog hxy : x ≤ y generalizing x y
    . exact symm <| this hc.symm <| le_of_not_le hxy
    refine hxy.eq_or_lt.elim id (fun hxy => h hxy |>.elim ?_)
    exists t.1, t.2
    rwa [← this]

-- TODO move this thing
open scoped RealInnerProductSpace

theorem zero_not_mem_segment_iff {V}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (a b : V) :
    0 ∉ segment ℝ a b ↔
    a ≠ 0 ∧ ∃ v, 0 ≤ ⟪a, v⟫ ∧ 0 < ⟪b, v⟫ := by
  constructor
  case mp =>
    intro h0
    have ha : a ≠ 0 := fun h => h0 <| h ▸ left_mem_segment ℝ _ _
    have hb : b ≠ 0 := fun h => h0 <| h ▸ right_mem_segment ℝ _ _
    refine ⟨ha, ‖a‖⁻¹ • a + ‖b‖⁻¹ • b, ?_⟩
    suffices : -1 < ⟪a, b⟫ / (‖a‖ * ‖b‖)
    . rw [← norm_pos_iff] at ha hb
      simp_rw [inner_add_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, pow_two,
        inv_mul_eq_div, mul_self_div_self]
      constructor
      . rw [← neg_le_iff_add_nonneg', ← neg_one_mul, ← le_div_iff ha,
          div_div, mul_comm]
        exact this.le
      . rw [← neg_lt_iff_pos_add, ← neg_one_mul, ← lt_div_iff hb,
          div_div, real_inner_comm]
        exact this
    suffices ⟪a, b⟫ / (‖a‖ * ‖b‖) ≠ -1 from this.lt_of_le' <|
      neg_le_of_abs_le <| abs_real_inner_div_norm_mul_norm_le_one _ _
    apply mt <| real_inner_div_norm_mul_norm_eq_neg_one_iff _ _ |>.mp
    push_neg
    rintro - r hr
    contrapose! h0 with hb; subst hb; clear ha hb
    refine ⟨-r / (-r + 1), 1 / (-r + 1), ?_, ?_, ?_, ?_⟩
    . rw [le_div_iff] <;> linarith
    . rw [le_div_iff] <;> linarith
    . rw [← add_div]
      exact div_self (by linarith)
    . rw [smul_smul, ← mul_div_right_comm, one_mul, ← add_smul,
        neg_div, neg_add_self, zero_smul]
  case mpr =>
    rintro ⟨ha, v, hv₁, hv₂⟩ ⟨x, y, hx, hy, hxy, h⟩
    rcases hy.eq_or_lt with rfl | hy
    . rw [add_zero] at hxy
      simp only [hxy, one_smul, zero_smul, add_zero, ha] at h
    apply congrArg (⟪·, v⟫) at h
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at h
    nlinarith


def aux.e : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  .symm <| (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp] theorem aux.e_apply_mk x y : e (x, y) = ![x, y] := rfl

-- TODO move this
@[simp] theorem EuclideanSpace.real_inner_two_apply (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp

@[simp] theorem EuclideanSpace.real_inner_two_apply_mk (a b c d : ℝ) :
    @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ ![a, b] ![c, d] = a * c + b * d := by
  simp

@[simp] theorem vec_two_ext {α} {a b c d : α} :
    ![a, b] = ![c, d] ↔ a = c ∧ b = d := by
  simp [Matrix.vecCons, Fin.cons_eq_cons]


-- @[simp] theorem EuclideanSpace.two_mk_sub_mk {𝕜} [IsROrC 𝕜] (a b c d : 𝕜) :
--     ![a, b] - ![c, d] = (![a - c, b - d] : EuclideanSpace 𝕜 (Fin 2)) := by
--   simp

-- TODO these theorems don't have to be a silly brute force:
-- you can prove that stuff is piecewise linear,
-- and then prove that the inner products of a piecewise linear function with
-- v are monotone as long as that's true for the control points

set_option maxHeartbeats 1000000 in
theorem aux.homotopy_l_injective_zero : ∀ t, Function.Injective (aux.homotopy_l 0 |>.curry t) := by
  rw [homotopy_l, linearHomotopy_timewise_injective_iff]
  intro x y hxy
  rw [← Subtype.coe_lt_coe] at hxy
  rw [mem_segment_iff_wbtw, ← e.toAffineEquiv.wbtw_map_iff, ← mem_segment_iff_wbtw]
  simp_rw [LinearEquiv.coe_toAffineEquiv, ContinuousLinearEquiv.coe_toLinearEquiv, map_zero]
  rw [segment_symm, zero_not_mem_segment_iff]
  simp only [ContinuousMap.coe_coe, zero_l_apply, zero_i_apply, succ_l_apply, succ_i_apply]
  constructor
  case left =>
    split_ifs <;> simp only [t0, t1, t2, t3] at * <;> try (exfalso; linarith)
    save
    all_goals
    . simp only [squareCoe, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
        p_zero, map_sub, e_apply_mk, sub_ne_zero]
      apply mt vec_two_ext.mp
      rintro ⟨h₁, h₂⟩
      norm_num1 at h₁ h₂ <;> linarith
  by_cases hy : (y : ℝ) ≤ 1/2 <;>
    [ exists ![0, 1]; exists ![1, 0] ] <;>
    constructor
  case pos.right | neg.right =>
    split_ifs <;> try (exfalso; linarith)
    all_goals
    . simp_rw [map_sub, squareCoe_mk, e_apply_mk, inner_sub_left,
        EuclideanSpace.real_inner_two_apply_mk, p_zero]
      norm_num1 <;> linarith
  all_goals
  . split_ifs <;> simp only [t0, t1, t2, t3] at * <;> try (exfalso; linarith)
    save
    all_goals
    . simp only [squareCoe, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
        p_zero, map_sub, e_apply_mk, inner_sub_left,
        EuclideanSpace.real_inner_two_apply_mk]
      norm_num1 <;> linarith

set_option maxHeartbeats 1000000 in
theorem aux.homotopy_i_injective_zero : ∀ t, Function.Injective (aux.homotopy_i 0 |>.curry t) := by
  rw [homotopy_i, linearHomotopy_timewise_injective_iff]
  intro x y hxy
  rw [← Subtype.coe_lt_coe] at hxy
  rw [mem_segment_iff_wbtw, ← e.toAffineEquiv.wbtw_map_iff, ← mem_segment_iff_wbtw]
  simp_rw [LinearEquiv.coe_toAffineEquiv, ContinuousLinearEquiv.coe_toLinearEquiv, map_zero]
  rw [segment_symm, zero_not_mem_segment_iff]
  simp only [ContinuousMap.coe_coe, zero_l_apply, zero_i_apply, succ_l_apply, succ_i_apply]
  constructor
  case left =>
    split_ifs <;> simp only [t0, t1, t2, t3] at * <;> try (exfalso; linarith)
    save
    all_goals
    . simp only [squareCoe, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
        p_zero, map_sub, e_apply_mk, sub_ne_zero]
      apply mt vec_two_ext.mp
      rintro ⟨h₁, h₂⟩
      norm_num1 at h₁ h₂ <;> linarith
  exists ![1, 0]
  constructor
  case right =>
    simp_rw [map_sub, squareCoe_mk, e_apply_mk, inner_sub_left, EuclideanSpace.real_inner_two_apply_mk]
    simpa using hxy
  split_ifs <;> simp only [t0, t1, t2, t3] at * <;> try (exfalso; linarith)
  save
  all_goals
  . simp only [squareCoe, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
      p_zero, map_sub, e_apply_mk, inner_sub_left,
      EuclideanSpace.real_inner_two_apply_mk]
    norm_num1 <;> linarith


theorem aux.homotopy_l_succ_eq n s t :
  homotopy_l (n+1) (s, t) =
    if h₁ : (t : ℝ) ≤ 1/4 then
      q 0 <| homotopy_i n (s, t0 t)
    else if h₂ : (t : ℝ) ≤ 2/4 then
      q 1 <| homotopy_l n (s, t1 t)
    else if h₃ : (t : ℝ) ≤ 3/4 then
      q 2 <| homotopy_l n (s, t2 t)
    else
      q 3 <| homotopy_l n (s, t3 t) := by
  simp only [← squareCoe_inj, homotopy_l, homotopy_i, linearHomotopy_apply, line_def, ContinuousMap.coe_coe]
  conv_lhs =>
    rw [aux.succ_l_apply n t, aux.succ_l_apply (n+1) t]
  split_ifs
  all_goals
  . rw [Prod.mk.injEq]
    simp only [squareCoe, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
      line_def_x, line_def_y, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul]
    constructor <;> linarith

theorem aux.homotopy_i_succ_eq n s t :
  homotopy_i (n+1) (s, t) =
    if h₁ : (t : ℝ) ≤ 1/4 then
      q 0 <| homotopy_l n (s, t0 t)
    else if h₂ : (t : ℝ) ≤ 2/4 then
      q 1 <| homotopy_l n (s, t1 t)
    else if h₃ : (t : ℝ) ≤ 3/4 then
      q 2 <| homotopy_l n (s, t2 t)
    else
      q 3 <| homotopy_l n (s, t3 t) := by
  simp only [← squareCoe_inj, homotopy_l, homotopy_i, linearHomotopy_apply, line_def, ContinuousMap.coe_coe]
  conv_lhs =>
    rw [aux.succ_i_apply n t, aux.succ_i_apply (n+1) t]
  split_ifs
  all_goals
  . rw [Prod.mk.injEq]
    simp only [squareCoe, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
      line_def_x, line_def_y, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul]
    constructor <;> linarith


-- TODO:
-- there are *so* many proofs where you just show the same thing twice:
-- once for L, once for I.
-- you could easily make all of these do both proofs at once with some light automation.


theorem aux.homotopy_l_injective_succ n t
  (ih_l : Function.Injective (homotopy_l n |>.curry t))
  (ih_i : Function.Injective (homotopy_i n |>.curry t)) :
    Function.Injective (homotopy_l (n+1) |>.curry t) := by
  apply Function.Injective.eq_iff at ih_l
  apply Function.Injective.eq_iff at ih_i
  simp only [ContinuousMap.Homotopy.curry_apply] at ih_l ih_i
  intro x y
  simp only [ContinuousMap.Homotopy.curry_apply,
    homotopy_l_succ_eq, linearHomotopy_apply, ContinuousMap.coe_coe]
  split_ifs <;> first
  | intro h
    have h_boundary := q_inter (by decide) h
    rw [← Subtype.coe_inj]
    simp only [homotopy_l_boundary, homotopy_i_boundary,
      t1_ne_zero, t2_ne_one, t3_ne_one] at h_boundary
    rcases h_boundary with ⟨hx | hx, hy | hy⟩ <;> try contradiction
    all_goals
    . exfalso
      rw [hx, hy] at h
      clear! x y ih_l ih_i
      rw [Prod.mk.injEq] at h
      revert h
      simp only [← Subtype.coe_inj, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
        homotopy_l, homotopy_i, linearHomotopy_apply, ContinuousMap.coe_coe,
        line_def_x, line_def_y, Path.source, Path.target, not_and, p_succ]
      rcases t with ⟨t, ht₀, ht₁⟩
      set v := (p n : ℝ)
      push_cast
      have hv₀ : 0 < v := p_pos
      have hv₁ : v ≤ 1/2 := p_le_half
      rintro ⟨h₁, h₂⟩; nlinarith
  | contrapose!
    intro hxy
    simpa only [ne_eq, q_inj, ih_l, ih_i, t0_inj, t1_inj, t2_inj, t3_inj] using hxy

theorem aux.homotopy_i_injective_succ n t
  (ih_l : Function.Injective (homotopy_l n |>.curry t)) :
    Function.Injective (homotopy_i (n+1) |>.curry t) := by
  apply Function.Injective.eq_iff at ih_l
  simp only [ContinuousMap.Homotopy.curry_apply] at ih_l
  intro x y
  simp only [ContinuousMap.Homotopy.curry_apply,
    homotopy_i_succ_eq, linearHomotopy_apply, ContinuousMap.coe_coe]
  split_ifs <;> first
  | intro h
    have h_boundary := q_inter (by decide) h
    rw [← Subtype.coe_inj]
    simp only [homotopy_l_boundary, homotopy_i_boundary,
      t1_ne_zero, t2_ne_one, t3_ne_one] at h_boundary
    rcases h_boundary with ⟨hx | hx, hy | hy⟩ <;> try contradiction
    all_goals
    . exfalso
      rw [hx, hy] at h
      clear! x y ih_l
      rw [Prod.mk.injEq] at h
      revert h
      simp only [← Subtype.coe_inj, q0_x, q0_y, q1_x, q1_y, q2_x, q2_y, q3_x, q3_y,
        homotopy_l, homotopy_i, linearHomotopy_apply, ContinuousMap.coe_coe,
        line_def_x, line_def_y, Path.source, Path.target, not_and, p_succ]
      rcases t with ⟨t, ht₀, ht₁⟩
      set v := (p n : ℝ)
      push_cast
      have hv₀ : 0 < v := p_pos
      have hv₁ : v ≤ 1/2 := p_le_half
      rintro ⟨h₁, h₂⟩; nlinarith
  | contrapose!
    intro hxy
    simpa only [ne_eq, q_inj, ih_l, t0_inj, t1_inj, t2_inj, t3_inj] using hxy

theorem aux.homotopy_injective t : (n : ℕ) →
  Function.Injective (homotopy_l n |>.curry t) ∧ Function.Injective (homotopy_i n |>.curry t)
| 0 => ⟨homotopy_l_injective_zero t, homotopy_i_injective_zero t⟩
| n + 1 =>
  let ⟨l, i⟩ := homotopy_injective t n
  ⟨homotopy_l_injective_succ n t l i, homotopy_i_injective_succ n t l⟩

theorem aux.homotopy_l_injective n t :
    Function.Injective (homotopy_l n |>.curry t) :=
  homotopy_injective t n |>.1

theorem aux.homotopy_i_injective n t :
    Function.Injective (homotopy_i n |>.curry t) :=
  homotopy_injective t n |>.2


section infDist

open Metric Set

-- the distance is sup Chebyshev.
lemma aux.infDist_le_l_zero {y} : infDist y (range (aux 0).1) ≤ 1 := by
  apply infDist_le_dist_of_mem (mem_range.mpr ⟨0, rfl⟩) |>.trans
  simp only [Prod.dist_eq, max_le, dist_le_one, implies_true]

lemma aux.infDist_le_i_zero {y} : infDist y (range (aux 0).2) ≤ 1 := by
  apply infDist_le_dist_of_mem (mem_range.mpr ⟨0, rfl⟩) |>.trans
  simp only [Prod.dist_eq, max_le, dist_le_one, implies_true]

-- TODO move these i guess?
def aux.q0_inv (x y : I)
    (hx : (x : ℝ) ≤ 1/2) (hy : (y : ℝ) ≤ 1/2) : I × I := by
  refine ⟨⟨2 * y, ?_⟩, ⟨2 * x, ?_⟩⟩
  all_goals
  . rw [mem_Icc]; constructor <;> linarith [x.2.1, y.2.1, x.2.2, y.2.2]
def aux.q1_inv (x y : I)
    (hx : (x : ℝ) ≤ 1/2) (hy : 1/2 ≤ (y : ℝ)) : I × I := by
  refine ⟨⟨2 * x, ?_⟩, ⟨2 * y - 1, ?_⟩⟩
  all_goals
  . rw [mem_Icc]; constructor <;> linarith [x.2.1, y.2.1, x.2.2, y.2.2]
def aux.q2_inv (x y : I)
    (hx : 1/2 ≤ (x : ℝ)) (hy : 1/2 ≤ (y : ℝ)) : I × I := by
  refine ⟨⟨2 - 2 * x, ?_⟩, ⟨2 * y - 1, ?_⟩⟩
  all_goals
  . rw [mem_Icc]; constructor <;> linarith [x.2.1, y.2.1, x.2.2, y.2.2]
def aux.q3_inv (x y : I)
    (hx : 1/2 ≤ (x : ℝ)) (hy : (y : ℝ) ≤ 1/2) : I × I := by
  refine ⟨⟨2 * y, ?_⟩, ⟨2 - 2 * x, ?_⟩⟩
  all_goals
  . rw [mem_Icc]; constructor <;> linarith [x.2.1, y.2.1, x.2.2, y.2.2]

@[simp] theorem aux.q0_inv_apply {x y} (hx hy) : q 0 (q0_inv x y hx hy) = (x, y) := by
  rw [Prod.mk.injEq]; simp only [← Subtype.coe_inj, q0_x, q0_y, q0_inv]
  constructor <;> linarith
@[simp] theorem aux.q1_inv_apply {x y} (hx hy) : q 1 (q1_inv x y hx hy) = (x, y) := by
  rw [Prod.mk.injEq]; simp only [← Subtype.coe_inj, q1_x, q1_y, q1_inv]
  constructor <;> linarith
@[simp] theorem aux.q2_inv_apply {x y} (hx hy) : q 2 (q2_inv x y hx hy) = (x, y) := by
  rw [Prod.mk.injEq]; simp only [← Subtype.coe_inj, q2_x, q2_y, q2_inv]
  constructor <;> linarith
@[simp] theorem aux.q3_inv_apply {x y} (hx hy) : q 3 (q3_inv x y hx hy) = (x, y) := by
  rw [Prod.mk.injEq]; simp only [← Subtype.coe_inj, q3_x, q3_y, q3_inv]
  constructor <;> linarith

lemma aux.range_l_succ n :
  range (aux (n+1)).1 =
    q 0 '' range (aux n).2 ∪
    q 1 '' range (aux n).1 ∪
    q 2 '' range (aux n).1 ∪
    q 3 '' range (aux n).1 := by
  simp only [aux, Nat.add_eq, Nat.add_zero, Path.trans_range, autoCast, Path.cast,
    Path.coe_mk_mk, Path.map_coe, Path.map_symm, Path.symm_range, range_comp, union_assoc]

lemma aux.range_i_succ n :
  range (aux (n+1)).2 =
    q 0 '' range (aux n).1 ∪
    q 1 '' range (aux n).1 ∪
    q 2 '' range (aux n).1 ∪
    q 3 '' range (aux n).1 := by
  simp only [aux, Nat.add_eq, Nat.add_zero, Path.trans_range, autoCast, Path.cast,
    Path.coe_mk_mk, Path.map_coe, Path.map_symm, Path.symm_range, range_comp, union_assoc]

lemma aux.infDist_le_l_succ n {y}
  {c : ℝ} (ih_l : ∀ z, infDist z (range (aux n).1) ≤ c) (ih_i : ∀ z, infDist z (range (aux n).2) ≤ c) :
    infDist y (range (aux (n+1)).1) ≤ c / 2 := by
  simp_rw [range_l_succ, infDist_eq_iInf, ← sInf_image', image_union, ← range_comp] at ih_l ih_i ⊢
  have lol S : BddBelow (dist y '' S) := ⟨0, fun _ ⟨x, _, hx⟩ => hx ▸ dist_nonneg⟩
  repeat
    rw [csInf_union
      (by simp only [bddBelow_union, range_comp, lol, and_self])
      (by simp only [union_nonempty, range_nonempty, or_self])
      (by simp only [bddBelow_union, range_comp, lol])
      (by simp only [union_nonempty, range_nonempty, or_self])]
  clear lol
  simp_rw [inf_le_iff, Function.comp]
  rcases y with ⟨x, y⟩
  by_cases hx : (x : ℝ) ≤ 1/2 <;> by_cases hy : (y : ℝ) ≤ 1/2
  all_goals
  . first
    | rw [← q0_inv_apply hx hy]
      refine .inl <| .inl <| .inl ?_
    | rw [← q1_inv_apply hx (le_of_not_le hy)]
      refine .inl <| .inl <| .inr ?_
    | rw [← q2_inv_apply (le_of_not_le hx) (le_of_not_le hy)]
      refine .inl <| .inr <| ?_
    | rw [← q3_inv_apply (le_of_not_le hx) hy]
      refine .inr <| ?_
    simp_rw [q_dist_map, div_eq_inv_mul, ← smul_eq_mul]
    rw [← smul_set_range, Real.sInf_smul_of_nonneg (by positivity)]
    gcongr
    apply_assumption

lemma aux.infDist_le_i_succ n {y}
  {c : ℝ} (ih_l : ∀ z, infDist z (range (aux n).1) ≤ c) :
    infDist y (range (aux (n+1)).2) ≤ c / 2 := by
  simp_rw [range_i_succ, infDist_eq_iInf, ← sInf_image', image_union, ← range_comp] at ih_l ⊢
  have lol S : BddBelow (dist y '' S) := ⟨0, fun _ ⟨x, _, hx⟩ => hx ▸ dist_nonneg⟩
  repeat
    rw [csInf_union
      (by simp only [bddBelow_union, range_comp, lol, and_self])
      (by simp only [union_nonempty, range_nonempty, or_self])
      (by simp only [bddBelow_union, range_comp, lol])
      (by simp only [union_nonempty, range_nonempty, or_self])]
  clear lol
  simp_rw [inf_le_iff, Function.comp]
  rcases y with ⟨x, y⟩
  by_cases hx : (x : ℝ) ≤ 1/2 <;> by_cases hy : (y : ℝ) ≤ 1/2
  all_goals
  . first
    | rw [← q0_inv_apply hx hy]
      refine .inl <| .inl <| .inl ?_
    | rw [← q1_inv_apply hx (le_of_not_le hy)]
      refine .inl <| .inl <| .inr ?_
    | rw [← q2_inv_apply (le_of_not_le hx) (le_of_not_le hy)]
      refine .inl <| .inr <| ?_
    | rw [← q3_inv_apply (le_of_not_le hx) hy]
      refine .inr <| ?_
    simp_rw [q_dist_map, div_eq_inv_mul, ← smul_eq_mul]
    rw [← smul_set_range, Real.sInf_smul_of_nonneg (by positivity)]
    gcongr
    apply_assumption

lemma aux.infDist_le : (n : ℕ) →
  (∀ y, infDist y (range (aux n).1) ≤ 1 / 2 ^ n) ∧ (∀ y, infDist y (range (aux n).2) ≤ 1 / 2 ^ n)
| 0 => by norm_num1; exact ⟨fun _ => infDist_le_l_zero, fun _ => infDist_le_i_zero⟩
| n + 1 =>
  let ⟨l, i⟩ := infDist_le n
  ⟨fun y => infDist_le_l_succ n l i |>.trans <| by
    rw [pow_succ', ← div_div, div_le_div_right (by positivity)],
  fun y => infDist_le_i_succ n l |>.trans <| by
    rw [pow_succ', ← div_div, div_le_div_right (by positivity)]⟩

theorem aux.infDist_le_l n {y} : infDist y (range (aux n).1) ≤ 1 / 2 ^ n :=
  aux.infDist_le n |>.1 y

theorem aux.infDist_le_i n {y} : infDist y (range (aux n).2) ≤ 1 / 2 ^ n :=
  aux.infDist_le n |>.2 y

end infDist

lemma aux.dist_le_l_zero : dist (α := C(I, I × I)) (aux 0).1 (aux 1).1 ≤ 1 := by
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  simp only [Prod.dist_eq, max_le, dist_le_one, implies_true]

lemma aux.dist_le_i_zero : dist (α := C(I, I × I)) (aux 0).2 (aux 1).2 ≤ 1 := by
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  simp only [Prod.dist_eq, max_le, dist_le_one, implies_true]

lemma aux.dist_le_l_succ n :
  dist (α := C(I, I × I)) (aux (n+1)).1 (aux (n+2)).1 ≤
    max
      (dist (α := C(I, I × I)) (aux n).1 (aux (n+1)).1)
      (dist (α := C(I, I × I)) (aux n).2 (aux (n+1)).2) / 2 := by
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  simp_rw [ContinuousMap.dist_eq_iSup, ContinuousMap.coe_coe]
  intro x
  conv_lhs => rw [succ_l_apply, succ_l_apply]
  rw [← max_div_div_right (by norm_num)]
  split_ifs
  all_goals
  . simp only [q_dist_map]
    rw [le_max_iff]
    simp_rw [div_le_div_right (c := (2 : ℝ)) (by positivity)]
    first
    | left
      apply le_ciSup (f := fun x => dist _ _)
    | right
      apply le_ciSup (f := fun x => dist _ _)
    rw [bddAbove_def]
    use 1
    rw [Set.forall_range_iff]
    intro i
    simp only [Prod.dist_eq, max_le, dist_le_one]

lemma aux.dist_le_i_succ n :
  dist (α := C(I, I × I)) (aux (n+1)).2 (aux (n+2)).2 ≤
    dist (α := C(I, I × I)) (aux n).1 (aux (n+1)).1 / 2 := by
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  simp_rw [ContinuousMap.dist_eq_iSup, ContinuousMap.coe_coe]
  intro x
  conv_lhs => rw [succ_i_apply, succ_i_apply]
  split_ifs
  all_goals
  . simp only [q_dist_map]
    simp_rw [div_le_div_right (c := (2 : ℝ)) (by positivity)]
    apply le_ciSup (f := fun x => dist _ _)
    rw [bddAbove_def]
    use 1
    rw [Set.forall_range_iff]
    intro i
    simp only [Prod.dist_eq, max_le, dist_le_one]

lemma aux.dist_le : (n : ℕ) →
  dist (α := C(I, I × I)) (aux n).1 (aux (n+1)).1 ≤ 1 / 2 ^ n ∧
  dist (α := C(I, I × I)) (aux n).2 (aux (n+1)).2 ≤ 1 / 2 ^ n
| 0 => by norm_num1; exact ⟨aux.dist_le_l_zero, aux.dist_le_i_zero⟩
| n + 1 =>
  let ⟨l, i⟩ := dist_le n
  ⟨dist_le_l_succ n |>.trans <| by
    rw [pow_succ', ← div_div, div_le_div_right (by positivity)]
    exact max_le l i,
  dist_le_i_succ n |>.trans <| by
    rw [pow_succ', ← div_div, div_le_div_right (by positivity)]
    exact l⟩

theorem aux.dist_le_l n :
    dist (α := C(I, I × I)) (aux n).1 (aux (n+1)).1 ≤ 1 / 2 ^ n :=
  aux.dist_le n |>.1

theorem aux.dist_le_i n :
    dist (α := C(I, I × I)) (aux n).2 (aux (n+1)).2 ≤ 1 / 2 ^ n :=
  aux.dist_le n |>.2



-- TODO TODO TODO!!!!!! instead of doing homotopy distances inductively too,
-- simply use the linearity stuff

lemma aux.dist_le_homotopy_l_zero : dist (α := C(I × I, I × I)) (homotopy_l 0) (homotopy_l 1) ≤ 1 := by
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  simp only [Prod.dist_eq, max_le, dist_le_one, implies_true]

lemma aux.dist_le_homotopy_i_zero : dist (α := C(I × I, I × I)) (homotopy_i 0) (homotopy_i 1) ≤ 1 := by
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  simp only [Prod.dist_eq, max_le, dist_le_one, implies_true]

-- TODO: you can recover the curve theorem from this one, I guess.
lemma aux.dist_le_homotopy_l_succ n :
  dist (α := C(I × I, I × I)) (homotopy_l (n+1)) (homotopy_l (n+2)) ≤
    max
      (dist (α := C(I × I, I × I)) (homotopy_l n) (homotopy_l (n+1)))
      (dist (α := C(I × I, I × I)) (homotopy_i n) (homotopy_i (n+1))) / 2 := by
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  simp_rw [ContinuousMap.dist_eq_iSup, ContinuousMap.coe_coe]
  rintro ⟨t, x⟩
  conv_lhs => rw [homotopy_l_succ_eq, homotopy_l_succ_eq]
  rw [← max_div_div_right (by norm_num)]
  split_ifs <;>
    simp only [q_dist_map] <;>
    rw [le_max_iff] <;>
    simp_rw [div_le_div_right (c := (2 : ℝ)) (by positivity)] <;>
    [ (right; apply le_ciSup (f := fun x => dist _ _));
      (left; apply le_ciSup (f := fun x => dist _ _));
      (left; apply le_ciSup (f := fun x => dist _ _));
      (left; apply le_ciSup (f := fun x => dist _ _)) ]
  all_goals
  . rw [bddAbove_def]
    use 1
    rw [Set.forall_range_iff]
    intro i
    simp only [Prod.dist_eq, max_le, dist_le_one]

lemma aux.dist_le_homotopy_i_succ n :
  dist (α := C(I × I, I × I)) (homotopy_i (n+1)) (homotopy_i (n+2)) ≤
    dist (α := C(I × I, I × I)) (homotopy_l n) (homotopy_l (n+1)) / 2 := by
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  simp_rw [ContinuousMap.dist_eq_iSup, ContinuousMap.coe_coe]
  rintro ⟨t, x⟩
  conv_lhs => rw [homotopy_i_succ_eq, homotopy_i_succ_eq]
  split_ifs <;>
    simp only [q_dist_map] <;>
    simp_rw [div_le_div_right (c := (2 : ℝ)) (by positivity)] <;>
    apply le_ciSup (f := fun x => dist _ _)
  all_goals
  . rw [bddAbove_def]
    use 1
    rw [Set.forall_range_iff]
    intro i
    simp only [Prod.dist_eq, max_le, dist_le_one]

lemma aux.dist_le_homotopy : (n : ℕ) →
  dist (α := C(I × I, I × I)) (homotopy_l n) (homotopy_l (n+1)) ≤ 1 / 2 ^ n ∧
  dist (α := C(I × I, I × I)) (homotopy_i n) (homotopy_i (n+1)) ≤ 1 / 2 ^ n
| 0 => by norm_num1; exact ⟨aux.dist_le_homotopy_l_zero, aux.dist_le_homotopy_i_zero⟩
| n + 1 =>
  let ⟨l, i⟩ := dist_le_homotopy n
  ⟨dist_le_homotopy_l_succ n |>.trans <| by
    rw [pow_succ', ← div_div, div_le_div_right (by positivity)]
    exact max_le l i,
  dist_le_homotopy_i_succ n |>.trans <| by
    rw [pow_succ', ← div_div, div_le_div_right (by positivity)]
    exact l⟩

theorem aux.dist_le_homotopy_l n :
    dist (α := C(I × I, I × I)) (homotopy_l n) (homotopy_l (n+1)) ≤ 1 / 2 ^ n :=
  aux.dist_le_homotopy n |>.1

theorem aux.dist_le_homotopy_i n :
    dist (α := C(I × I, I × I)) (homotopy_i n) (homotopy_i (n+1)) ≤ 1 / 2 ^ n :=
  aux.dist_le_homotopy n |>.2


theorem aux.dist_le_in_homotopy_l n {t t'} :
    dist (α := C(I, I × I)) (homotopy_l n |>.curry t) (homotopy_l n |>.curry t') ≤ 1 / 2 ^ n := by
  have h := dist_le_l n
  rw [ContinuousMap.dist_le_iff_of_nonempty] at h ⊢
  peel h with x h
  simp_rw [ContinuousMap.Homotopy.curry_apply, homotopy_l, linearHomotopy_apply,
    ContinuousMap.coe_coe, Prod.dist_eq, Subtype.dist_eq, line_def_x, line_def_y,
    max_le_iff, Real.dist_eq] at h ⊢
  refine ⟨le_trans ?_ h.1, le_trans ?_ h.2⟩
  . set p := (aux n).1 x |>.1
    set q := (aux (n+1)).1 x |>.1
    convert_to |(t' - t) * (p - q : ℝ)| ≤ |(p - q : ℝ)|
    . ring_nf
    rw [abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    rw [← Real.dist_eq, ← Subtype.dist_eq]
    apply dist_le_one
  . set p := (aux n).1 x |>.2
    set q := (aux (n+1)).1 x |>.2
    convert_to |(t' - t) * (p - q : ℝ)| ≤ |(p - q : ℝ)|
    . ring_nf
    rw [abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    rw [← Real.dist_eq, ← Subtype.dist_eq]
    apply dist_le_one

theorem aux.dist_le_in_homotopy_i n {t t'} :
    dist (α := C(I, I × I)) (homotopy_i n |>.curry t) (homotopy_i n |>.curry t') ≤ 1 / 2 ^ n := by
  have h := dist_le_i n
  rw [ContinuousMap.dist_le_iff_of_nonempty] at h ⊢
  peel h with x h
  simp_rw [ContinuousMap.Homotopy.curry_apply, homotopy_i, linearHomotopy_apply,
    ContinuousMap.coe_coe, Prod.dist_eq, Subtype.dist_eq, line_def_x, line_def_y,
    max_le_iff, Real.dist_eq] at h ⊢
  refine ⟨le_trans ?_ h.1, le_trans ?_ h.2⟩
  . set p := (aux n).2 x |>.1
    set q := (aux (n+1)).2 x |>.1
    convert_to |(t' - t) * (p - q : ℝ)| ≤ |(p - q : ℝ)|
    . ring_nf
    rw [abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    rw [← Real.dist_eq, ← Subtype.dist_eq]
    apply dist_le_one
  . set p := (aux n).2 x |>.2
    set q := (aux (n+1)).2 x |>.2
    convert_to |(t' - t) * (p - q : ℝ)| ≤ |(p - q : ℝ)|
    . ring_nf
    rw [abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    rw [← Real.dist_eq, ← Subtype.dist_eq]
    apply dist_le_one


-- we use the I shaped one to build the infinite hilbert curve
theorem aux.i_cauchy : CauchySeq (α := C(I, I × I)) (fun n => (aux n).2) := by
  apply cauchySeq_of_le_geometric_two 2
  intro n
  rw [div_self (by positivity)]
  apply dist_le_i

noncomputable def aux.hilbertCurve' : C(I, I × I) :=
  cauchySeq_tendsto_of_complete aux.i_cauchy |>.choose

open Filter

theorem aux.hilbertCurve'_spec : Tendsto (fun n => (aux n).2) atTop (nhds hilbertCurve') :=
  cauchySeq_tendsto_of_complete aux.i_cauchy |>.choose_spec

theorem aux.hilbertCurve'_eq_iff x y :
    hilbertCurve' x = y ↔ Tendsto (fun n => (aux n).2 x) atTop (nhds y) := by
  have := ContinuousMap.continuous_eval_const x |>.tendsto hilbertCurve' |>.comp hilbertCurve'_spec
  exact ⟨fun h => h ▸ this, tendsto_nhds_unique this⟩

-- TODO: wiggle this around
@[simp]
private theorem p_tendsto_zero : Tendsto p atTop (nhds 0) := by
  unfold p
  rw [tendsto_subtype_rng]
  dsimp only
  conv => congr; ext; rw [← neg_add', ← inv_zpow', zpow_add₀ (by positivity)]
  rw [Set.Icc.coe_zero, ← zero_mul (2⁻¹ ^ 1)]
  apply Tendsto.mul_const
  apply tendsto_pow_atTop_nhds_zero_of_lt_one <;> norm_num


def aux.partialHomotopyBuilder n {f : C(I, I × I)} (h : ContinuousMap.Homotopy (aux n).2 f) :
    ContinuousMap.Homotopy (aux 0).2 f :=
  match n with
  | 0 => h
  | n + 1 => partialHomotopyBuilder n (homotopy_i n |>.trans h)

def aux.partialHomotopy n : ContinuousMap.Homotopy (X := I) (Y := I × I) (aux 0).2 (aux n).2 :=
  partialHomotopyBuilder n (.refl _)


theorem aux.dist_partialHomotopyBuilder n {f₁ f₂} h₁ h₂ :
    dist (α := C(I × I, I × I))
      (partialHomotopyBuilder n (f := f₁) h₁) (partialHomotopyBuilder n (f := f₂) h₂) =
    dist (α := C(I × I, I × I)) h₁ h₂ := by
  induction n using Nat.recAux with
  | zero => rfl
  | succ n ih =>
    unfold partialHomotopyBuilder
    erw [ih]
    rw [ContinuousMap.Homotopy.dist_trans, dist_self, max_eq_right_iff]
    apply dist_nonneg

theorem aux.dist_le_partialHomotopy n :
    dist (α := C(I × I, I × I)) (partialHomotopy n) (partialHomotopy (n + 1)) ≤ 1 / 2 ^ n := by
  simp only [partialHomotopy, partialHomotopyBuilder, Nat.add_eq, Nat.add_zero]
  rw [dist_partialHomotopyBuilder, ← ContinuousMap.Homotopy.refl_trans_refl,
    ContinuousMap.Homotopy.dist_trans]
  apply max_le
  . rw [ContinuousMap.dist_le_iff_of_nonempty]
    rintro ⟨t, x⟩
    simp only [ContinuousMap.coe_coe, ContinuousMap.Homotopy.refl_apply]
    have : (aux n).2 x = homotopy_i n (0, x)
    . simp only [ContinuousMap.coe_coe, homotopy_i, ContinuousMap.Homotopy.apply_zero]
    rw [this]; clear this
    revert x
    simp_rw [← ContinuousMap.Homotopy.curry_apply, ← ContinuousMap.dist_le_iff_of_nonempty]
    apply dist_le_in_homotopy_i
  . rw [ContinuousMap.dist_le_iff_of_nonempty]
    rintro ⟨t, x⟩
    simp_rw [ContinuousMap.coe_coe, ContinuousMap.Homotopy.refl_apply]
    revert x
    rw [← ContinuousMap.dist_le_iff_of_nonempty]
    apply dist_le_i

theorem aux.partialHomotopy_cauchy : CauchySeq (α := C(I × I, I × I)) (fun n => aux.partialHomotopy n) := by
  apply cauchySeq_of_le_geometric_two 2
  intro n
  rw [div_self (by positivity)]
  apply dist_le_partialHomotopy

noncomputable def aux.homotopy' : C(I × I, I × I) :=
  cauchySeq_tendsto_of_complete aux.partialHomotopy_cauchy |>.choose

theorem aux.homotopy'_spec : Tendsto (fun n => partialHomotopy n) atTop (nhds homotopy') :=
  cauchySeq_tendsto_of_complete aux.partialHomotopy_cauchy |>.choose_spec


lemma aux.partialHomotopyBuilder_apply n {f} h t x :
    (∀ m < n,
      partialHomotopyBuilder n (f := f) h (rightHalf^[m] (leftHalf t), x) =
      homotopy_i m (t, x)) ∧
    partialHomotopyBuilder n (f := f) h (rightHalf^[n] t, x) =
    h (t, x) := by
  induction n using Nat.recAux generalizing t with
  | zero => simp [partialHomotopyBuilder]
  | succ n ih =>
    conv => congr; ext m; rw [Nat.lt_succ_iff_lt_or_eq, or_comm]
    simp only [forall_eq_or_imp, partialHomotopyBuilder, Nat.add_eq, Nat.add_zero,
      Function.iterate_succ, Function.comp_apply]
    specialize ih (homotopy_i n |>.trans h)
    exact ⟨⟨ih (leftHalf t) |>.2 |>.trans <| ContinuousMap.Homotopy.trans_leftHalf_apply _ _, (ih t).1⟩,
      ih (rightHalf t) |>.2 |>.trans <| ContinuousMap.Homotopy.trans_rightHalf_apply _ _⟩

theorem aux.partialHomotopy_apply_lt n m (hm : m < n) {t x : I}
  (t_lo : 2 ^ m * (1 - t : ℝ) ≤ 1) (t_hi : 1 ≤ 2 ^ (m+1) * (1 - t : ℝ)) :
    partialHomotopy n (t, x) =
    homotopy_i m (⟨2 ^ (m+1) * (t - (1 - 1 / 2 ^ m)), by
      rw [Set.mem_Icc]
      ring_nf at *
      simp_rw [← mul_pow, div_mul_cancel _ (show (2 : ℝ) ≠ 0 by norm_num), one_pow] at *
      set v : ℝ := 2 ^ m
      constructor <;> linarith⟩, x) := by
  convert partialHomotopyBuilder_apply n _ _ x |>.1 m hm
  simp only [leftHalf, rightHalf, ContinuousMap.coe_mk]
  clear hm
  rw [← Subtype.coe_inj]
  induction m using Nat.recAux generalizing t with
  | zero => simp; linarith
  | succ m ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [eq_div_iff two_ne_zero, mul_comm, add_comm, ← add_neg_eq_iff_eq_add]
    specialize ih (t := ⟨2 * t - 1, _⟩) _ _
    . rw [Set.mem_Icc]
      rw [pow_succ] at t_hi
      set v : ℝ := 2 ^ (m + 1)
      have : 2 ≤ v := le_self_pow one_le_two m.succ_ne_zero
      constructor <;> [ nlinarith only [t_lo, this]; nlinarith only [t_hi, this] ]
    . convert t_lo using 1
      ring1
    . convert t_hi using 1
      ring1
    convert ih using 3
    rw [← Subtype.coe_inj]
    ring1

theorem aux.partialHomotopy_curry_lt n m (hm : m < n) {t : I}
  (t_lo : 2 ^ m * (1 - t : ℝ) ≤ 1) (t_hi : 1 ≤ 2 ^ (m+1) * (1 - t : ℝ)) :
    (partialHomotopy n).curry t =
    (homotopy_i m).curry ⟨2 ^ (m+1) * (t - (1 - 1 / 2 ^ m)), by
      rw [Set.mem_Icc]
      ring_nf at *
      simp_rw [← mul_pow, div_mul_cancel _ (show (2 : ℝ) ≠ 0 by norm_num), one_pow] at *
      set v : ℝ := 2 ^ m
      constructor <;> linarith⟩ := by
  simp_rw [DFunLike.ext_iff, ContinuousMap.Homotopy.curry_apply]
  intro
  apply partialHomotopy_apply_lt <;> assumption

end Aux




noncomputable def hilbertCurve : Path (X := I × I) (0, 0) (1, 0) where
  toFun := aux.hilbertCurve'
  source' := by
    apply tendsto_nhds_unique <| ContinuousMap.continuous_eval_const 0 |>.tendsto aux.hilbertCurve'
      |>.comp aux.hilbertCurve'_spec
    simp only [Function.comp_def, ContinuousMap.coe_coe, Path.source, Prod.tendsto_iff]
    exact ⟨tendsto_const_nhds, p_tendsto_zero⟩
  target' := by
    apply tendsto_nhds_unique <| ContinuousMap.continuous_eval_const 1 |>.tendsto aux.hilbertCurve'
      |>.comp aux.hilbertCurve'_spec
    simp only [Function.comp_def, ContinuousMap.coe_coe, Path.target, Prod.tendsto_iff]
    exact ⟨tendsto_const_nhds, p_tendsto_zero⟩

open Filter

theorem hilbertCurve_spec : Tendsto (β := C(I, I × I)) (fun n => (aux n).2) atTop (nhds hilbertCurve) :=
  aux.hilbertCurve'_spec

theorem hilbertCurve_eq_iff x y :
    hilbertCurve x = y ↔ Tendsto (fun n => (aux n).2 x) atTop (nhds y) :=
  aux.hilbertCurve'_eq_iff x y

theorem hilbertCurve_surjective : Function.Surjective hilbertCurve := by
  intro y
  suffices ∃ f : ℕ → I, Tendsto (fun n => (aux n).2 (f n)) atTop (nhds y) by
    rcases this with ⟨f, hf⟩
    have ⟨a, ϕ, hϕ, ha⟩ := CompactSpace.tendsto_subseq f
    replace hϕ := hϕ.tendsto_atTop
    exists a
    apply Eq.symm ∘ tendsto_nhds_unique (hf.comp hϕ)
    exact ContinuousMap.continuous_eval.tendsto _ |>.comp <|
      show Tendsto (fun n => (_, (f ∘ ϕ) n)) atTop (nhds (_, a)) from
        Prod.tendsto_iff _ _ |>.mpr ⟨hilbertCurve_spec.comp hϕ, ha⟩
  have h n : ∃ x, dist y ((aux n).2 x) ≤ 1 / 2 ^ n
  . obtain ⟨_, ⟨x, _, hx⟩, hy⟩ := IsCompact.exists_infDist_eq_dist (s := Set.range (aux n).2)
      (isCompact_range <| map_continuous _) (Set.range_nonempty _) y
    exists x
    rw [← hy]
    apply aux.infDist_le_i
  choose f hf using h
  exists f
  rw [tendsto_iff_dist_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := 0))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1/2) (by norm_num) (by norm_num))
    (fun _ => dist_nonneg)
  rw [Pi.le_def]
  intro n
  rw [dist_comm, div_pow, one_pow]
  exact hf n




noncomputable def hilbertHomotopy' : ContinuousMap.Homotopy (X := I) (Y := I × I) (aux 0).2 hilbertCurve where
  toFun := aux.homotopy'
  map_zero_left x := by
    apply tendsto_nhds_unique <| ContinuousMap.continuous_eval_const (0, x) |>.tendsto _
      |>.comp aux.homotopy'_spec
    simp [Function.comp]
  map_one_left x := by
    apply tendsto_nhds_unique <| ContinuousMap.continuous_eval_const (1, x) |>.tendsto _
      |>.comp aux.homotopy'_spec
    simpa [Function.comp] using ContinuousMap.continuous_eval_const x |>.tendsto _
      |>.comp hilbertCurve_spec

theorem hilbertHomotopy'_injective {t} (ht : t < 1) : Function.Injective (hilbertHomotopy'.curry t) := by
  let m := Nat.log2 ⌊1 / (1 - t : ℝ)⌋₊
  replace ht : 0 < (1 - t : ℝ) := by linarith only [show (t : ℝ) < 1 from ht]
  convert aux.homotopy_i_injective m _ using 2
  apply tendsto_nhds_unique <| ContinuousMap.continuous_eval_const t |>.comp ContinuousMap.continuous_curry |>.tendsto _
    |>.comp aux.homotopy'_spec
  simp only [Function.comp]
  apply tendsto_atTop_of_eventually_const (i₀ := m + 1)
  intro n hn
  exact aux.partialHomotopy_curry_lt n m (Nat.lt_of_succ_le hn) (t := t)
    (by
      rw [← le_div_iff ht, ← Nat.cast_ofNat, ← Nat.cast_pow, ← Nat.le_floor_iff (by positivity)]
      apply Nat.log2_self_le
      rw [ne_eq, Nat.floor_eq_zero, not_lt]
      exact one_le_one_div ht (sub_le_self _ t.2.1))
    (by
      rw [← div_le_iff ht, ← Nat.cast_ofNat (n := 2), ← Nat.cast_pow]
      refine Nat.lt_floor_add_one _ |>.trans_le ?_ |>.le
      norm_cast
      rw [← Nat.lt_iff_add_one_le]
      apply Nat.lt_log2_self)

end HilbertCurve
