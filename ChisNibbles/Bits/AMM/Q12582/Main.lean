module

public import ChisNibbles.Bits.AMM.Q12582.Spec
import Mathlib


section ForMathlib

-- it seems as if Nat.dist is not well loved
theorem Nat.dist_eq_natAbs_sub {x y : ℕ} :
    x.dist y = (x - y : ℤ).natAbs := by
  grind [dist]

@[simp] theorem Nat.coe_dist_eq_abs_sub {x y : ℕ} :
    x.dist y = |(x - y : ℤ)| := by
  grind [dist]

theorem Nat.coe_dist_eq_dist {x y : ℕ} :
    x.dist y = Dist.dist x y := by
  rw [dist_eq_natAbs_sub]
  aesop


theorem better_abs_le
    {G : Type*} [AddGroup G] [Lattice G] [AddLeftMono G] [AddRightMono G]
    {a b : G} :
    |a| ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  rw [abs_le', neg_le]; tauto


namespace Set

open Pointwise

@[to_additive Icc_sub_Icc_subset]
theorem Icc_div_Icc_subset'
    {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
    (a b c d : α) :
    Icc a b / Icc c d ⊆ Icc (a / d) (b / c) := by
  grw [div_eq_mul_inv, inv_Icc, Icc_mul_Icc_subset', ← div_eq_mul_inv, ← div_eq_mul_inv]

-- and friends...

end Set


namespace Int

@[simps! (nameStem := "int")] instance instFloorDiv : FloorDiv ℤ ℤ where
  floorDiv b a := if a ≤ 0 then 0 else b / a
  floorDiv_gc a ha b c := by simp [ha.not_ge, Int.le_ediv_iff_mul_le ha, mul_comm]
  floorDiv_nonpos := by grind only
  zero_floorDiv := by simp

@[simps! (nameStem := "int") -isSimp] instance instCeilDiv : CeilDiv ℤ ℤ where
  ceilDiv b a := if a ≤ 0 then 0 else (b + a - 1) / a
  ceilDiv_gc a ha b c := by simp [ha.not_ge, Int.ediv_le_iff_le_mul ha, mul_comm]
  ceilDiv_nonpos := by grind only
  zero_ceilDiv a := by grind only [← Int.ediv_eq_zero_of_lt]

@[simps! (nameStem := "nat")] instance instFloorDivNat : FloorDiv ℕ ℤ where
  floorDiv b a := b / (a : ℤ)
  floorDiv_gc a ha b c := by simp [Int.le_ediv_iff_mul_le (natCast_pos.mpr ha), mul_comm]
  floorDiv_nonpos := by simp
  zero_floorDiv := by simp

@[simps! (nameStem := "nat") -isSimp] instance instCeilDivNat : CeilDiv ℕ ℤ where
  ceilDiv b a := (b + a - 1) / (a : ℤ)
  ceilDiv_gc a ha b c := by simp [Int.ediv_le_iff_le_mul (natCast_pos.mpr ha), mul_comm]
  ceilDiv_nonpos := by simp
  zero_ceilDiv := by grind only [← Int.ediv_eq_zero_of_lt]

end Int

-- TODO:
-- you could prove
-- ∀ c, 0 < c → a ⌈/⌉ b ≤ a ⌊/⌋ b + c (or whatever)
-- for appropriate (linear?) orders here i guess



namespace SignType

@[simp, norm_cast] lemma coe_prod
    {α : Type*} [CommMonoidWithZero α] [HasDistribNeg α]
    {ι : Type*} (s : Finset ι) (f : ι → SignType) :
    cast (α := α) (∏ i ∈ s, f i) = ∏ i ∈ s, cast (f i) := by
  induction s using Finset.cons_induction <;> aesop

@[simp] theorem intCast_mem_range_iff
    (R : Type*) [Ring R] [CharZero R]
    (x : ℤ) :
    (x : R) ∈ Set.range cast ↔ x ∈ Set.range cast := by
  peel with y
  conv_lhs => rw [eq_comm]
  conv_rhs => rw [eq_comm]
  cases y <;> simp [← neg_eq_iff_eq_neg, ← Int.cast_neg]

theorem range_cast
    (R : Type*) [Zero R] [One R] [Neg R] :
    Set.range (cast (α := R)) = {-1, 0, 1} := by
  simp [range_eq]; grind

@[irreducible] def ofIntUnit (x : ℤˣ) : SignType := sign (x : ℤ)

@[simp] theorem coe_ofIntUnit
    (R : Type*) [Ring R] x : (ofIntUnit x : R) = x := by
  rw [← intCast_cast, ofIntUnit, sign_apply]
  rcases Int.isUnit_eq_one_or x.isUnit with h | h
    <;> simp_rw [h] <;> rfl

end SignType


namespace IsModuleTopology

theorem continuous_of_affineMap
    {R V P W Q : Type*}
    [TopologicalSpace R] [Ring R]
    [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsModuleTopology R V]
    [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
    [AddCommGroup W] [Module R W] [TopologicalSpace W] [ContinuousAdd W] [ContinuousSMul R W]
    [AddTorsor W Q] [TopologicalSpace Q] [IsTopologicalAddTorsor Q]
    (φ : P →ᵃ[R] Q) :
    Continuous φ :=
  φ.continuous_linear_iff.mp <| continuous_of_linearMap φ.linear

end IsModuleTopology




@[simp] theorem Sum.smul_elim
  {M R : Type*} [SMul M R] {α β : Type*}
  (a : M) (x : α → R) (y : β → R) :
    a • (Sum.elim x y) = Sum.elim (a • x) (a • y) := by
  aesop


-- this is like this for consistency with map_add etc.,
-- but it makes me sad that these silly theorems get such short names
theorem Matrix.map_neg
    {m n α β : Type*} [Neg α] [Neg β]
    (f : α → β) (hf : ∀ x, f (-x) = -f x)
    (A : Matrix m n α) :
    map (-A) f = -map A f := by
  ext i j; simp [hf]


namespace RingHom
open Matrix
variable
  {m n R S : Type*} [Fintype n]
  [NonAssocSemiring R] [NonAssocSemiring S]
  (f : R →+* S)

theorem map_comp_vecMul (M : Matrix n m R)
    (v : n → R) : f ∘ (v ᵥ* M) = (f ∘ v) ᵥ* M.map f :=
  funext fun _ => map_vecMul ..

theorem map_comp_mulVec (M : Matrix m n R)
    (v : n → R) : f ∘ (M *ᵥ v) = M.map f *ᵥ (f ∘ v) :=
  funext fun _ => map_mulVec ..
end RingHom

-- weakens IsOrderedRing to IsOrderedAddMonoid, and uses affine equivalence instead
lemma image_extremePoints'
    {R E F : Type*}
    [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (f : E ≃ᵃ[R] F) (s : Set E) :
    f '' Set.extremePoints R s = Set.extremePoints R (f '' s) := by
  ext b
  obtain ⟨a, rfl⟩ := EquivLike.surjective f b
  have : ∀ x y, f '' openSegment R x y = openSegment R (f x) (f y) :=
    image_openSegment _ f.toAffineMap
  simp only [mem_extremePoints, (EquivLike.surjective f).forall,
    (EquivLike.injective f).mem_set_image, (EquivLike.injective f).eq_iff, ← this]

lemma preimage_extremePoints_subset
    {R E F : Type*}
    [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    {f : E →ᵃ[R] F} (hf : Function.Injective f) (s : Set F) :
    f ⁻¹' Set.extremePoints R s ⊆ Set.extremePoints R (f ⁻¹' s) := by
  intro x
  simp only [Set.mem_preimage, mem_extremePoints_iff_left]
  grind only [= Set.mem_image, ! image_openSegment _ f]


namespace IsOpen

open scoped Pointwise

variable
  {R E : Type*}
  [Ring R] [PartialOrder R] [IsOrderedAddMonoid R] [ZeroLEOneClass R] [IsDomain R] [DenselyOrdered R]
  [TopologicalSpace R] [IsTopologicalRing R] [PerfectSpace R]
  [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul R E]
  [Nontrivial E]

private lemma extremePoints_empty.aux {s : Set R} (h : IsOpen s) :
    Set.extremePoints R s = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  have ⟨a, ha⟩ : ∃ a : R, 0 < a ∧ a < 1 := exists_between zero_lt_one

  let T := {x | y + a * x ∈ s ∧ y - (1 - a) * x ∈ s}
  have hT : IsOpen T :=
    .inter (h.preimage (by fun_prop)) (h.preimage (by fun_prop))
  have h0T : 0 ∈ T := by simpa [T] using extremePoints_subset hy

  have ⟨x, ⟨hx₁, hx₂⟩, hx0⟩ :=
    PerfectSpace.not_isolated (0 : R) |> nhdsWithin_neBot.mp <|
      hT.mem_nhds_iff.mpr h0T
  rw [mem_extremePoints_iff_left] at hy
  absurd hy.2 _ hx₁ _ hx₂ ⟨1 - a, a, ?_⟩ <;>
    (clear * - ha hx0; simp; grind)

theorem extremePoints_empty {s : Set E} (h : IsOpen s) :
    Set.extremePoints R s = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x
  have ⟨f, hf, hx⟩ : ∃ f : R →ᵃ[R] E, Function.Injective f ∧ x ∈ Set.range f := by
    have ⟨y, hy⟩ : ∃ y : E, y ≠ 0 := exists_ne 0
    exists (LinearMap.id.smulRight y).toAffineMap + .const R R x
    rw [← AffineMap.linear_injective_iff]
    simp [smul_left_injective R hy]
  suffices f ⁻¹' Set.extremePoints R s = ∅ by
    grind only [Set.preimage_eq_empty_iff, = Set.disjoint_left]
  apply Set.eq_empty_of_subset_empty
  grw [preimage_extremePoints_subset hf s]

  rw [extremePoints_empty.aux]
  exact h.preimage <| IsModuleTopology.continuous_of_affineMap f

end IsOpen


namespace Matrix.IsTotallyUnimodular

/-
section lift
variable
  {m n R : Type*} [CommRing R] [CharZero R]
  {A : Matrix m n R} (hA : A.IsTotallyUnimodular)

noncomputable def lift_val : Matrix m n ℤ :=
  of <| fun i j => hA.apply i j |>.choose

omit [CharZero R] in
@[simp, grind! .] theorem lift_spec : (lift_val hA).map (↑) = A := by
  ext; simp [lift_val]; grind only [usr Exists.choose_spec]

@[simp, grind! .] theorem lift : IsTotallyUnimodular (lift_val hA) := by
  have h := hA
  rw [isTotallyUnimodular_iff] at ⊢ h
  peel h with k f g h
  have : det (hA.lift_val.submatrix f g) = det (A.submatrix f g) := by
    simp [Int.cast_det, ← submatrix_map]
  rwa [← this, SignType.intCast_mem_range_iff] at h

/-
would be nice for this to lift the total unimodularity of the matrix as well
-/
instance :
    CanLift (Matrix m n R) (Matrix m n ℤ) (·.map (↑)) IsTotallyUnimodular where
  prf _ h := ⟨h.lift_val, h.lift_spec⟩
end lift
-/


section map
variable
  {m n : Type*}
  {R : Type*} [CommRing R]
  {S : Type*} [CommRing S]
  (f : R →+* S)

theorem map {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    IsTotallyUnimodular (A.map f) := by
  peel hA with k a b ha hb h
  erw [submatrix_map, ← f.map_det]
  rcases h with ⟨y, hy⟩
  exists y
  rw [← hy, SignType.map_cast]

theorem map_intCast {A : Matrix m n ℤ} (hA : A.IsTotallyUnimodular) :
    IsTotallyUnimodular (R := R) (A.map (↑)) :=
  hA.map (Int.castRingHom R)
end map


theorem det
    {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    {A : Matrix n n R} (hA : A.IsTotallyUnimodular) :
    det A ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff_fintype] at hA
  specialize hA n id id
  simpa


theorem smul_sign_row
    {m n R : Type*} [CommRing R]
    {A : Matrix m n R} (hA : IsTotallyUnimodular A)
    {B : Matrix m n R}
    (h : ∀ i, ∃ s : SignType, B.row i = (s : R) • A.row i) :
    IsTotallyUnimodular B := by
  peel hA with k f g hf hg hA
  set A' := A.submatrix f g
  choose s hs using h
  replace hs : B.submatrix f g = of (fun i j => (s ∘ f) i * A' i j) :=
    ext fun i j => congr($(hs _) _)
  simp_rw [hs, det_mul_column] -- TODO: det_mul_row, det_mul_column are mislabelled?
  norm_cast
  rcases hA with ⟨y, hy⟩
  exists (∏ i, (s ∘ f) i) * y
  simp [hy]

theorem smul_sign_col
    {m n R : Type*} [CommRing R]
    {A : Matrix m n R} (hA : IsTotallyUnimodular A)
    {B : Matrix m n R}
    (h : ∀ j, ∃ s : SignType, B.col j = (s : R) • A.col j) :
    IsTotallyUnimodular B :=
  transpose <| smul_sign_row (transpose hA) h


theorem fromRows_neg_self
    {m n R : Type*} [CommRing R]
    {A : Matrix m n R} (hA : IsTotallyUnimodular A) :
    IsTotallyUnimodular (fromRows A (-A)) := by
  apply smul_sign_row (A := fromRows A A)
  . convert hA.submatrix (id ⊕ᵥ id) id
    ext i j; cases i <;> simp
  . intro i
    cases i with
    | inl i => exists  1; ext j; simp
    | inr i => exists -1; ext j; simp


private theorem of_plus_minus.aux
    {n : ℕ}
    {R : Type*} [CommRing R]
    {A : Matrix (Fin n) (Fin n) R}
    (h : ∀ i, ∃ j j' : Option (Fin n),
      A.row i = (setOf (· ∈ j)).indicator 1 - (setOf (· ∈ j')).indicator 1) :
    A.det ∈ Set.range SignType.cast := by
  induction n with
  | zero =>
    exists 1; simp
  | succ n ih =>
    by_cases h₁ : ∃ (i : _) (j : Option _) (s : SignType),
        A.row i = (setOf (· ∈ j)).indicator (fun _ => ↑s)
    . rcases h₁ with ⟨i, j, s, hi⟩
      rw [row] at hi
      simp_rw [A.det_eq_sum_mul_adjugate_row i, hi]
      cases j with
      | none => exists 0; simp
      | some j
      suffices s * A.adjugate j i ∈ Set.range SignType.cast by
        simpa [Pi.single_apply]
      simp_rw [adjugate_fin_succ_eq_det_submatrix]
      specialize ih (A := A.submatrix i.succAbove j.succAbove) fun i₀ => by
        clear * - h
        specialize h (i.succAbove i₀)
        rcases h with ⟨j₁, j₁', h⟩
        exists j₁.bind (finSuccEquiv' j), j₁'.bind (finSuccEquiv' j)
        ext j₀
        convert congr($h <| j.succAbove j₀) using 1
        cases j₁ <;> cases j₁' <;> simp [Set.indicator_apply, Pi.single_apply] <;> lia
      rcases ih with ⟨y, hy⟩; rw [← hy]
      existsi s * ((-1) ^ (i + j : ℕ) * y)
      simp
    . push_neg at h₁
      suffices ∀ i, ∑ j, A.row i j = 0 by
        dsimp [row] at this
        rw [A.det_eq_sum_row_mul_submatrix_succAbove_succAbove_det 0 0 (by simp [this])]
        exists 0; simp [this]
      intro i
      specialize h i
      specialize h₁ i
      rcases h with ⟨j, j', h⟩; simp_rw [h] at h₁ ⊢
      clear * - h₁
      contrapose! h₁ with hj
      match j, j' with
      | some x, none => exists x,  1; ext; simp
      | none, some x => exists x, -1; ext; simp [Pi.single_neg]
      | none, none | some _, some _ => simp at hj


/--
A matrix where each row is zero except for at most one 1 and -1 is TU.
-/
theorem of_row_plus_minus
    {m n : Type*}
    {R : Type*} [CommRing R]
    {A : Matrix m n R}
    (h : ∀ i, ∃ j j' : Option n,
      A.row i = (setOf (· ∈ j)).indicator 1 - (setOf (· ∈ j')).indicator 1) :
    IsTotallyUnimodular A := by
  classical
  intro k f g hf hg
  apply of_plus_minus.aux
  intro i₀
  specialize h (f i₀)
  rcases h with ⟨j₁, j₁', h⟩
  exists j₁.bind g.partialInv, j₁'.bind g.partialInv
  ext j₀
  convert congr($h <| g j₀) using 1
  have := g.partialInv_of_injective hg
  unfold Function.IsPartialInv at this
  cases j₁ <;> cases j₁' <;> simp [this, Set.indicator_apply, Pi.single_apply]

/--
A matrix where each column is zero except for at most one 1 and -1 is TU.
-/
theorem of_col_plus_minus
    {m n : Type*}
    {R : Type*} [CommRing R]
    {A : Matrix m n R}
    (h : ∀ j, ∃ i i' : Option m,
      A.col j = (setOf (· ∈ i)).indicator 1 - (setOf (· ∈ i')).indicator 1) :
    IsTotallyUnimodular A :=
  transpose <| of_row_plus_minus h



private theorem of_row_consecutive_ones.aux
    {n : ℕ}
    {R : Type*} [CommRing R]
    {A : Matrix (Fin n) (Fin n) R}
    (h : ∀ i, ∃ u : Interval (Fin n), A.row i = Set.indicator u 1) :
    A.det ∈ Set.range SignType.cast := by
  classical
  cases n with
  | zero => exists 1; simp
  | succ n
  -- consider matrix of differences of adjacent columns
  let B := Matrix.of fun i j => A i j - j.cases 0 (A i ·.castSucc)
  have : A.det = B.det := by
    apply det_eq_of_forall_col_eq_smul_add_pred 1
      <;> simp [B]
  rw [this]; clear this

  -- this has at most one +1 and -1 in each row
  apply det ∘ of_row_plus_minus
  peel h with i h
  rcases h with ⟨u, h⟩
  rw [funext_iff] at h
  cases u with
  | bot =>
    exists none, none
    ext j
    simp_all [B]
    cases j using Fin.cases <;> simp
  | coe u =>
    rcases u with ⟨⟨l, r⟩, h⟩
    exists l, finSuccEquivLast r.succ
    ext j
    simp_all [B, finSuccEquivLast, Set.indicator_apply, Pi.single_apply]
    cases j using Fin.cases <;> simp <;> grind only [usr Fin.val_succ, = Fin.val_castSucc]

/--
A binary matrix where each row has consecutive 1s is TU.
-/
theorem of_row_consecutive_ones
    {m n : Type*} [LinearOrder n]
    {R : Type*} [CommRing R]
    {A : Matrix m n R}
    (h : ∀ i, ∃ u : Set n, u.OrdConnected ∧ A.row i = Set.indicator u 1) :
    IsTotallyUnimodular A := by
  classical
  intro k f g hf hg
  -- wlog that the inclusion of rows is monotone
  wlog g_mono : Monotone g generalizing g
  . let e := Tuple.sort g
    specialize this (g ∘ e) (hg.comp e.injective) (Tuple.monotone_sort g)
    set B := A.submatrix f g
    rw [show A.submatrix f (g ∘ e) = B.reindex (.refl _) e.symm by simp [B],
      det_reindex, Equiv.refl_symm, Equiv.trans_refl] at this
    rcases this with ⟨y, hy⟩
    exists .ofIntUnit e.sign * y
    simp_rw [SignType.coe_mul, SignType.coe_ofIntUnit, hy]
    rw [← mul_assoc]
    norm_cast; simp

  -- claim: 1s are consecutive in the submatrix
  apply of_row_consecutive_ones.aux
  intro i
  specialize h (f i)
  rcases h with ⟨u, hu, h⟩
  rw [funext_iff] at h
  let v := g ⁻¹' u
  have hv : v.OrdConnected := hu.preimage_mono g_mono
  -- convert OrdConnected set to an Interval for use in aux
  cases v.eq_empty_or_nonempty with
  | inl hv =>
    subst v
    exists ⊥
    ext j; simp_all [← Set.mem_preimage]
  | inr v_ne =>
    -- annoyingly there is no ConditionallyCompleteLinearOrder on Fintypes
    -- without first assuming nonemptiness...
    cases k
    . exists ⊥; ext j; exact j.elim0
    rw [v_ne.ordConnected_iff_of_bdd'] at hv
    let V : NonemptyInterval _ :=
      { toProd := (sInf v, sSup v), fst_le_snd := sInf_le_sSup v_ne }
    change g ⁻¹' u = V at hv
    exists V
    ext j; simp_all [Set.indicator_apply, ← Set.mem_preimage]

/--
A binary matrix where each column has consecutive 1s is TU.
-/
theorem of_col_consecutive_ones
    {m n : Type*} [LinearOrder m]
    {R : Type*} [CommRing R]
    {A : Matrix m n R}
    (h : ∀ j, ∃ u : Set m, u.OrdConnected ∧ A.col j = Set.indicator u 1) :
    IsTotallyUnimodular A :=
  transpose <| of_row_consecutive_ones h

end Matrix.IsTotallyUnimodular


end ForMathlib




open Matrix -- globally!!! how exciting.

def slicePolyhedron
    {m n : Type*} [Fintype n]
    {R : Type*} [NonUnitalNonAssocSemiring R] [LE R]
    (A : Matrix m n R) (b : m → R) : Set (n → R) :=
  {x | A *ᵥ x ≤ b}

theorem mem_slicePolyhedron
    {m n : Type*} [Fintype n]
    {R : Type*} [NonUnitalNonAssocSemiring R] [LE R]
    (A : Matrix m n R) (b : m → R) (x : n → R) :
    x ∈ slicePolyhedron A b ↔ A *ᵥ x ≤ b :=
  Iff.rfl

theorem convex_slicePolyhedron
    {m n : Type*} [Fintype n]
    {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    (A : Matrix m n R) (b : m → R) :
    Convex R (slicePolyhedron A b) :=
  convex_halfSpace_le A.mulVecLin.isLinear b

theorem isClosed_slicePolyhedron
    {m n : Type*} [Fintype n]
    {R : Type*} [NonUnitalNonAssocSemiring R] [Preorder R]
    [TopologicalSpace R] [OrderClosedTopology R] [IsTopologicalSemiring R]
    (A : Matrix m n R) (b : m → R) :
    IsClosed (slicePolyhedron A b) := by
  apply isClosed_le <;> fun_prop



namespace Matrix.IsTotallyUnimodular


variable
  {m n : Type*} [Fintype m] [Fintype n]
  {R : Type*}
  -- these assumptions (should) just imply that R is a subfield of ℝ
  [NontriviallyNormedField R] [LinearOrder R] [IsOrderedRing R] [Archimedean R] [OrderClosedTopology R]
  {A : Matrix m n ℤ} (hA : A.IsTotallyUnimodular)

variable (R) in
include hA in
omit [Archimedean R] in
/--
Extreme points of a TU slice polytope are integral.
TODO: factor this through total dual integrality. and use StrongDual maybe?
-/
theorem extremePoints_slicePolyhedron_integral
    (b : m → ℤ) :
    Set.extremePoints R (slicePolyhedron (R := R) (A.map (↑)) ((↑) ∘ b)) ⊆
    Set.range (Int.cast ∘ ·) := by
  classical
  intro x hx

  set P := slicePolyhedron (R := R) (A.map (↑)) ((↑) ∘ b)
  have hxP : x ∈ P := extremePoints_subset hx

  -- consider rows corresponding to saturated constraints
  let I : Finset m := {i | (A.map (↑) *ᵥ x) i = b i}
  let A' : Matrix I n ℤ := A.submatrix (↑) id
  have hA' : IsTotallyUnimodular A' := hA.submatrix _ _

  -- the submatrix formed of these rows must have trivial kernel
  let A'ₗ := (A'.map (β := R) (↑)).mulVecLin
  let U := A'ₗ.ker
  have hU : U = ⊥ := by
    -- this sure is a lot of lines
    by_contra! hU

    let S := ⋂ i ∈ Iᶜ, {x : n → R | (A.map (↑) *ᵥ x) i < b i}
    have hS : IsOpen S := by
      apply isOpen_biInter_finset
      intro i hi
      let f (x : n → R) : R := (A.map (↑) *ᵥ x) i
      show IsOpen {x | f x < b i}
      apply isOpen_lt <;> fun_prop
    have hxS : x ∈ S := by
      simp only [S, Finset.mem_compl, Set.mem_iInter, Set.mem_setOf_eq, I, Finset.mem_filter_univ]
      intro i
      specialize hxP i
      clear * - hxP; lia

    let f : U →ᵃ[R] (n → R) :=
      (Submodule.subtype _).toAffineMap + AffineMap.const R _ x
    have hf : Function.Injective f := by rw [← AffineMap.linear_injective_iff]; simp [f]

    have hx' : 0 ∈ f ⁻¹' S ∩ Set.extremePoints R (f ⁻¹' P) := by
      grw [← preimage_extremePoints_subset hf]
      simp [f]; tauto
    have hSP : f ⁻¹' S ⊆ f ⁻¹' P := by
      rintro ⟨d, hd⟩
      show d + x ∈ S → d + x ∈ P
      simp_rw [S, P, Set.mem_iInter, Set.mem_setOf, mem_slicePolyhedron]
      intro hic i
      by_cases hi : i ∈ I
      case neg => simpa using hic i (Finset.mem_compl.mpr hi) |>.le
      clear hic
      replace hd := congr($hd ⟨i, hi⟩)
      simp only [mulVecBilin_apply, mulVec, A'ₗ, A', map_apply, submatrix_apply, id_eq,
        Pi.zero_apply, dotProduct_add] at hd ⊢
      rw [hd, zero_add]
      exact hxP i
    grw [inter_extremePoints_subset_extremePoints_of_subset hSP] at hx'

    replace hS := hS.preimage <| show Continuous f by
      rw [← AffineMap.continuous_linear_iff]
      simp [f, continuous_subtype_val]
    have _ : Nontrivial U := U.nontrivial_iff_ne_bot.mpr hU
    have _ : PerfectSpace U := perfectSpace_of_module R _
    simp [hS.extremePoints_empty] at hx'

  -- i.e. its row space is ⊤
  have hV : Submodule.span R (Set.range (A'.map (β := R) (↑)).row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Submodule.finrank_eq_zero] at hU
    rw [← A'ₗ.finrank_range_add_finrank_ker, ← rank_eq_finrank_span_row,
      rank_eq_finrank_span_cols, ← range_mulVecLin, hU, add_zero]

  -- hence you can select a square invertible submatrix
  have ⟨f, hf⟩ : ∃ f : n → I, IsUnit (A'.submatrix f id |>.map (β := R) (↑)) := by
    simp_rw [← linearIndependent_rows_iff_isUnit]
    have ⟨κ, a, B, hB⟩ := Module.exists_basis_of_span_of_flat _ hV
    have e := B.indexEquiv (Pi.basisFun R n)
    exists a ∘ e.symm
    convert (B.reindex e).linearIndependent using 1
    funext i; simp [hB, row_map, row_submatrix]
  set A'' : Matrix n n ℤ := A'.submatrix f id
  -- which is also invertible over ℤ, since it is TU
  have hA'' : Invertible A'' := IsUnit.invertible <| by
    have : A''.det ∈ ({-1, 0, 1} : Set ℤ) :=
      SignType.range_cast _ ▸ (hA'.submatrix _ _).det
    rw [isUnit_iff_isUnit_det] at hf ⊢
    rw [Int.isUnit_iff]
    erw [← (Int.castRingHom R).map_det, isUnit_iff_ne_zero, Int.cast_ne_zero] at hf
    clear_value A''; clear * - this hf; grind
  -- and maps x to an integral vector
  let b'' : n → ℤ := b ∘ (↑) ∘ f
  have hxA'' : A''.map (↑) *ᵥ x = (↑) ∘ b'' := funext fun i =>
    Finset.mem_filter_univ (f i).1 |>.mp (f i).2

  -- so x is itself integral
  replace hxA'' : x = A''⁻¹.map (↑) *ᵥ ((↑) ∘ b'') := by
    simp [← hxA'', ← map_mul_intCast]
  erw [← (Int.castRingHom R).map_comp_mulVec] at hxA''
  simp [hxA'']

include hA in
private lemma slicePolyhedron_has_integral.aux_real
    (b : m → ℤ)
    (h : (slicePolyhedron (R := ℝ) (A.map (↑)) ((↑) ∘ b)).Nonempty) :
    (slicePolyhedron A b).Nonempty := by
  classical
  set P := slicePolyhedron (R := ℝ) (A.map (↑)) ((↑) ∘ b)
  rcases h with ⟨x, hx⟩

  -- restrict to a compact region P' containing x
  let A' : Matrix (m ⊕ n ⊕ n) n ℤ := fromRows A <| fromRows 1 (-1)
  have hA' : IsTotallyUnimodular A' :=
    hA.fromRows_unitlike <| by
      rintro h (i | i) <;> [ exists i, .pos ; exists i, .neg ]
      all_goals
        ext j; simp [Pi.single_apply, one_apply]; grind
  let b' : m ⊕ n ⊕ n → ℤ := b ⊕ᵥ (⌈‖x‖⌉ ⊕ᵥ ⌈‖x‖⌉)
  let P' := slicePolyhedron (R := ℝ) (A'.map (↑)) ((↑) ∘ b')
  have P'_spec : P' = P ∩ Metric.closedBall 0 ⌈‖x‖⌉ := by
    ext y
    rw [Set.mem_inter_iff]
    simp_rw [P, P', A', b', mem_slicePolyhedron, fromRows_map, fromRows_mulVec,
      Sum.comp_elim, Sum.elim_le_elim_iff]
    apply Iff.rfl.and
    rw [Matrix.map_neg (Int.cast (R := ℝ)) (by simp),
      Matrix.map_one (Int.cast (R := ℝ)) (by simp) (by simp),
      neg_mulVec, one_mulVec,
      Pi.le_def, Pi.le_def, ← forall_and]
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by simp [Int.ceil_nonneg])]
    refine forall_congr' fun i => ?_
    rewrite [Real.norm_eq_abs, abs_le, neg_le, and_comm]
    rfl
  have hP' : IsCompact P' := by
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_slicePolyhedron ..)
    rw [Metric.isBounded_iff_subset_closedBall 0, P'_spec]
    exact ⟨⌈‖x‖⌉, Set.inter_subset_right⟩
  replace hx : x ∈ P' := by simp [P'_spec, hx, Int.le_ceil]

  -- P' has an extreme point, which is integral
  have ⟨z, hz⟩ := hP'.extremePoints_nonempty ⟨x, hx⟩
  have := extremePoints_slicePolyhedron_integral ℝ hA' b' hz
  have _ : CanLift ℝ ℤ (↑) (· ∈ Set.range Int.cast) := ⟨by simp⟩
  lift z to n → ℤ
  . clear * - this; aesop
  replace hz : z ∈ slicePolyhedron A' b' := by
    apply extremePoints_subset at hz
    erw [mem_slicePolyhedron, ← (Int.castRingHom ℝ).map_comp_mulVec, Pi.le_def] at hz
    simp_rw [Function.comp_apply, Int.coe_castRingHom, Int.cast_le] at hz
    exact hz
  exact ⟨z, hz ∘' Sum.inl⟩

theorem slicePolyhedron_has_integral
    {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
    [Algebra R ℝ] [FaithfulSMul R ℝ] [SMulPosMono R ℝ]
    {A : Matrix m n ℤ} (hA : A.IsTotallyUnimodular)
    (b : m → ℤ)
    (h : (slicePolyhedron (R := R) (A.map (↑)) ((↑) ∘ b)).Nonempty) :
    (slicePolyhedron A b).Nonempty := by
  apply slicePolyhedron_has_integral.aux_real hA
  rcases h with ⟨x, hx⟩
  exists algebraMap R ℝ ∘ x
  rw [mem_slicePolyhedron, Pi.le_def] at hx ⊢
  peel hx with i hx
  convert algebraMap_mono ℝ hx using 0
  simp [RingHom.map_mulVec]

include hA in
open scoped Pointwise in
/--
A "division property" for slice polyhedra.
-/
theorem slicePolyhedron_add_eq
  (b₁ b₂ : m → ℤ)
  (h : ∃ μ₁ μ₂ : ℤ,
      μ₁ ≥ 0 ∧ μ₂ ≥ 0 ∧ ¬ (μ₁ = 0 ∧ μ₂ = 0) ∧
      μ₂ • b₁ = μ₁ • b₂) :
    slicePolyhedron A (b₁ + b₂) = slicePolyhedron A b₁ + slicePolyhedron A b₂ := by
  apply subset_antisymm
  . rcases h with ⟨μ₁, μ₂, hμ₁, hμ₂, hμ, hb⟩
    replace hμ : 0 < (μ₁ + μ₂ : ℚ) := by norm_cast; lia
    intro z h
    rw [Set.mem_add]
    simp_rw [mem_slicePolyhedron] at *

    let A' : Matrix (m ⊕ m) n ℤ := fromRows A (-A)
    have hA' : IsTotallyUnimodular A' := hA.fromRows_neg_self
    let b' : m ⊕ m → ℤ := b₁ ⊕ᵥ (b₂ - A *ᵥ z)
    have h : (slicePolyhedron (R := ℚ) (A'.map (↑)) ((↑) ∘ b')).Nonempty := by
      exists (μ₁ / (μ₁ + μ₂) : ℚ) • ((↑) ∘ z)
      simp_rw [mem_slicePolyhedron, A', b']
      rw [mulVec_smul, ← smul_le_smul_iff_of_pos_left (α := ℚ) (a := μ₁ + μ₂) hμ,
        smul_smul, mul_div_assoc', mul_div_cancel_left₀ _ hμ.ne']
      norm_cast at hμ ⊢
      simp only [fromRows_map, fromRows_mulVec, Sum.smul_elim, Sum.comp_elim, Sum.elim_le_elim_iff]
      repeat erw [← (Int.castRingHom ℚ).map_comp_mulVec]
      constructor
      -- we do this ext'd because some relevant lemmas aren't around :(
      all_goals
        intro i
        simp only [Int.coe_castRingHom, Function.comp_apply, Pi.smul_apply, Pi.sub_apply,
          zsmul_eq_mul]
        norm_cast
        revert i
      . change μ₁ • (A *ᵥ z) ≤ (μ₁ + μ₂) • b₁
        grw [h, smul_add, add_smul, hb]
      . change μ₁ • (-A *ᵥ z) ≤ (μ₁ + μ₂) • (b₂ - A *ᵥ z)
        suffices μ₂ • (A *ᵥ z) ≤ (μ₁ + μ₂) • b₂ by
          rw [neg_mulVec]
          linear_combination this
        grw [h, smul_add, add_smul, hb]

    apply hA'.slicePolyhedron_has_integral at h
    rcases h with ⟨x, hx⟩
    simp_rw [mem_slicePolyhedron, A', b'] at hx
    rw [fromRows_mulVec, Sum.elim_le_elim_iff, neg_mulVec] at hx
    rcases hx with ⟨hx, hy⟩
    exact ⟨x, hx, z - x, by rw [mulVec_sub]; linear_combination hy, by simp⟩
  . rintro _ ⟨x₁, h₁, x₂, h₂, rfl⟩
    dsimp [slicePolyhedron] at *
    rw [mulVec_add]
    solve_by_elim [add_le_add]

include hA in
open scoped Pointwise in
theorem slicePolyhedron_nsmul_eq
  (b : m → ℤ) {n : ℕ} (hn : 0 < n) :
    slicePolyhedron A (n • b) = n • slicePolyhedron A b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn; clear hn
  rw [zero_add]
  induction n with
  | zero => simp
  | succ n ih
  rw [succ_nsmul]
  conv_rhs => rw [succ_nsmul, ← ih]
  apply hA.slicePolyhedron_add_eq
  exists n + 1, 1
  norm_cast; simp


end Matrix.IsTotallyUnimodular

namespace AMM.Q12582

/-!
some theory of "events" where segments start/end, for a better-behaved timeline.
we could avoid requiring a linear order on passengers for our application if we instead
quotient events having the same time, but i just like this way more.
-/
section event

inductive Side | left | right deriving DecidableEq, Fintype
instance : LinearOrder Side :=
  .lift' (fun | .left => false | .right => true) <| by
    unfold Function.Injective; aesop
@[simp] theorem Side.left_lt_right : Side.left < .right := rfl

@[ext] structure Event {α : Type*} (_ : α → NonemptyInterval ℤ) where
  i : α
  side : Side
deriving DecidableEq, Fintype

namespace Event

variable
  {α : Type*} [Fintype α] [LinearOrder α]
  {f : α → NonemptyInterval ℤ}

def base (a : Event f) : ℤ :=
  match a.side with
  | .left  => f a.i |>.fst
  | .right => f a.i |>.snd

abbrev toKey (a : Event f) : ℤ ×ₗ Side ×ₗ α :=
  toLex (a.base, toLex (a.side, a.i))

open Event in
@[simps! -isSimp] instance : LinearOrder (Event f) :=
  .lift' toKey <| by
    unfold Function.Injective; aesop


def toRealKey (a : Event f) : ℝ ×ₗ Side :=
  toLex (a.base, a.side)

omit [Fintype α] in
theorem toRealKey_mono : Monotone (toRealKey (f := f)) := by
  simp only [Monotone, le_def, toRealKey, Prod.Lex.toLex_le_toLex, Int.cast_lt, Int.cast_inj]
  grind only

@[simps!] def untilReal (t : ℝ) : LowerSet (Event f) where
  carrier := toRealKey ⁻¹' Set.Iic (toLex (t, .left))
  lower' := isLowerSet_Iic _ |>.preimage toRealKey_mono

omit [Fintype α] in
theorem mem_untilReal t a :
    a ∈ untilReal (f := f) t ↔ toRealKey a ≤ toLex (t, .left) := by
  rfl

/--
True iff segment i is active after events in s have occurred
-/
def activeAt (s : LowerSet (Event f)) (i : α) : Prop :=
  ⟨i, .left⟩ ∈ s ∧ ¬ ⟨i, .right⟩ ∈ s

omit [Fintype α] in
theorem untilReal.spec t a :
    activeAt (untilReal (f := f) t) a ↔ t ∈ (f a).map Int.castOrderHom := by
  simp [activeAt, mem_untilReal, toRealKey, Prod.Lex.toLex_le_toLex, base, NonemptyInterval.mem_def]
  grind only

end Event

end event


open Event in
public theorem solution : Spec.Solution := by
  classical
  intro Car _ _ α _ span

  -- linearly order the passengers
  obtain ⟨_, -⟩ := exists_wellOrder α

  -- k := #cars
  -- τ := times up to having an equivalent set of passengers
  let k := Fintype.card Car
  letI τ := LowerSet (Event span)
  have hk : 0 < k := Fintype.card_pos

  -- construct inhabitation matrix; it is TU by consecutive-ones criterion
  let A : Matrix τ α ℤ := .of fun s i =>
    if activeAt s i then 1 else 0
  have hA : IsTotallyUnimodular A := .of_col_consecutive_ones fun i => by
    exists {s | activeAt s i}
    constructor
    . simp_rw [Set.ordConnected_def, Set.mem_setOf_eq, Set.Icc, Set.setOf_subset_setOf]
      grind only [activeAt, SetLike.le_def]
    ext s; simp [A, Set.indicator_apply]

  -- size t := number of passengers on the train at time t
  let (eq := size_def) size : τ → ℤ := A *ᵥ 1
  -- TODO: is it more convenient to have this be a Nat vector?

  -- augmented system which supports the bounds we need is also TU
  let A' : Matrix ((τ ⊕ α) ⊕ (τ ⊕ α)) α ℤ :=
    fromRows (fromRows A 1) (fromRows (-A) (-1))
  have hA' : IsTotallyUnimodular A' := by
    convert hA.fromRows_one.fromRows_neg_self; simp
  have A'_spec u₁ u₂ l₁ l₂ x :
      x ∈ slicePolyhedron A' ((u₁ ⊕ᵥ u₂) ⊕ᵥ (l₁ ⊕ᵥ l₂)) ↔
      A *ᵥ x ∈ Set.Icc (-l₁) u₁ ∧ x ∈ Set.Icc (-l₂) u₂ := by
    simp only [mem_slicePolyhedron, A', neg_le (a := l₁), neg_le (a := l₂),
      fromRows_mulVec, one_mulVec, neg_mulVec, Sum.elim_le_elim_iff, Set.mem_Icc]
    tauto

  -- the constraint vector of bounds for a single car
  let b' : (τ ⊕ α) ⊕ (τ ⊕ α) → ℤ :=
    (size ⌈/⌉ k ⊕ᵥ 1) ⊕ᵥ (-(size ⌊/⌋ k) ⊕ᵥ 0)

  -- the 1 vector is a valid solution to the constraint multiplied by #cars
  -- ("every person is allocated to a total of 1 car")
  have : 1 ∈ slicePolyhedron A' (k • b') := by
    suffices (k • (size ⌊/⌋ k) ≤ size ∧ size ≤ k • (size ⌈/⌉ k)) ∧ 1 ≤ (k : α → ℤ) by
      simpa only [Sum.smul_elim, nsmul_eq_mul, mul_one, mul_zero, smul_neg, A'_spec,
        ← size_def, Set.mem_Icc, neg_neg, neg_zero, zero_le_one, true_and, b']
    clear_value size k; clear * - hk
    rw [← le_floorDiv_iff_smul_le hk, ← ceilDiv_le_iff_le_smul hk, Pi.le_def (x := 1)]
    dsimp; lia

  -- by the division property we can find simultaneous allocations for all cars
  rw [hA'.slicePolyhedron_nsmul_eq _ hk, Set.mem_nsmul_iff_sum] at this
  rcases this with ⟨f, this⟩
  -- which satisfies the constraints in matrix form
  replace :
      (∀ i j, |A *ᵥ f i - A *ᵥ f j| ≤ 1) ∧
      (∀ a, ∃ i, flip f a = Pi.single i 1) := by
    rcases this with ⟨hf, f_sum⟩
    simp_rw [b', A'_spec, neg_neg, neg_zero] at hf
    choose hf_sz hf using hf
    constructor
    . intro i j
      suffices size ⌈/⌉ k - size ⌊/⌋ k ≤ 1 by
        have h := Set.sub_mem_sub (hf_sz i) (hf_sz j)
        grw [Set.Icc_sub_Icc_subset] at h
        rw [← neg_sub, Set.mem_Icc, ← better_abs_le] at h
        exact h.trans this
      simp_rw [Pi.floorDiv_def, Pi.ceilDiv_def, Pi.sub_def, Pi.le_def, Pi.one_apply]
      intro i
      rw [sub_le_iff_le_add', ceilDiv_le_iff_le_smul hk]
      -- this part is (basically) a theorem in latest mathlib i think
      by_contra!
      replace this := this.le
      rw [← le_floorDiv_iff_smul_le hk] at this
      clear * - this; lia
    . clear * - hf f_sum
      intro a
      replace hf i a : 0 ≤ f i a ∧ f i a ≤ 1 := by
        clear * - hf
        simp [Set.mem_Icc, Pi.le_def] at hf; grind only
      replace f_sum : ∑ i, f i a = 1 := by
        rw [funext_iff] at f_sum
        convert f_sum a; simp
      have ⟨i, _, hi⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero <| f_sum.trans_ne one_ne_zero
      replace hi : f i a = 1 := by
        clear * - hf hi; grind only
      have hj : ∀ j ≠ i, f j a = 0 := by
        suffices ∀ j ∈ ({i}ᶜ : Finset _), f j a = 0 by simpa
        rw [← Finset.sum_eq_zero_iff_of_nonneg]
        . rw [← Finset.sum_compl_add_sum {i}, Finset.sum_singleton'] at f_sum
          lia
        . grind only
      exists i
      ext j
      simp only [flip, Pi.single_apply]; grind only
  rcases this with ⟨f_diff, hf⟩

  -- and upgrade it to a function from passengers to cars
  choose f' hf using hf
  open scoped Finset in
  replace f_diff t i j :
      Nat.dist
        #{p | activeAt (f := span) t p ∧ f' p = i}
        #{p | activeAt (f := span) t p ∧ f' p = j} ≤ 1 := by
    suffices this i : (A *ᵥ f i) t = #{p | activeAt (f := span) t p ∧ f' p = i}
    . simp_rw [Nat.dist_eq_natAbs_sub, ← this]
      zify; apply f_diff
    clear * - hf
    simp_rw [funext_iff, Pi.single_apply, flip] at hf
    rw [Finset.card_filter, mulVec, dotProduct]
    push_cast
    congr; ext x
    simp [A]; grind
  clear * - f_diff; rename' f' => f

  have e : Car ≃ Fin k := Fintype.equivFin _
  exists e.symm ∘ f
  intro t _ s c₁ c₂
  simp_rw [s, ← untilReal.spec, Finset.filter_filter, Function.comp_apply, e.symm_apply_eq]
  clear * - f_diff
  apply f_diff -- NOTE: grind fails this lol (it gets confused by f_diff i guess)

end AMM.Q12582
