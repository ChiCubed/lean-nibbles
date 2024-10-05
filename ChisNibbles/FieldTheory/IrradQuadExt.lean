-- TODO: minimise imports
import Mathlib

/-!
# A quadratic extension that is not radical

In char ≠ 2, every quadratic field extension E/F is (simple) radical:
E = F(α) for some α ∈ E satisfying ∃ n > 0, α ^ n ∈ F.

This is also true in char 2 when E is finite (for trivial reasons).

In this file I construct a quadratic field extension that is not radical.
(this has *probably* been done before in the human world, I didn't check)
-/

/-
man, dealing with fields is so annoying at the moment. i think most of it
is that typeclass inference seems to take forever, and that there are a
handful of missing instances / definitions. it's also the only area of maths
that seems to repeatedly bluescreen my laptop
-/


-- a little fun bag of lemmas
section trace_pow_expChar
  variable {R : Type*} [CommRing R] (n : ℕ) [ExpChar R n]

  open Polynomial in
  lemma Matrix.charpoly_pow_expChar
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι R) :
      charpoly (A ^ n) = (charpoly A).map (frobenius R n) := by
    have hn : 0 < n := expChar_pos R n

    unfold charpoly charmatrix
    simp_rw [map_pow, RingHom.mapMatrix_apply]
    rw [← expand_inj hn,
      ← map_expand, expand_char, expand_eq_comp_X_pow, comp_eq_aeval,
      ← det_pow, AlgHom.map_det]
    congr
    simp_rw [map_sub, map_pow, AlgHom.mapMatrix_apply, scalar_apply, map_map]
    simp only [diagonal_map, aeval_zero, aeval_X]
    erw [← diagonal_pow, ← scalar_apply]
    rw [show aeval (X ^ n) ∘ C = C by ext; simp]

    obtain hι | hι := isEmpty_or_nonempty ι
    . obtain rfl := Subsingleton.allEq A 0
      simp [zero_pow_eq, hn.ne', charpoly]
    haveI : ExpChar (Matrix ι ι R[X]) n := expChar_of_injective_ringHom
      (f := scalar ι) (fun _ _ => scalar_inj.mp) n

    rw [sub_pow_expChar_of_commute]
    apply scalar_commute _ fun _ => .all _ _

  open Matrix in
  theorem LinearMap.trace_pow_expChar
    {M : Type*} [AddCommGroup M] [Module R M]
    (l : M →ₗ[R] M) :
      trace R M (l ^ n) = trace R M l ^ n := by
    classical
    have hn : 0 < n := expChar_pos R n

    by_cases H : ∃ s : Finset M, Nonempty (Basis s R M)
    case neg =>
      simp only [trace, H, ↓reduceDIte, zero_apply,
        ne_eq, not_false_eq_true, hn.ne', zero_pow]
    rcases H with ⟨s, ⟨b⟩⟩
    obtain rfl | hs := s.eq_empty_or_nonempty
    . obtain rfl : l = 0 := by apply b.ext; simp
      simp only [ne_eq, not_false_eq_true, map_zero, zero_pow, hn.ne']
    haveI : Nonempty s := by simpa using hs

    simp_rw [trace_eq_matrix_trace R b, trace_eq_neg_charpoly_coeff]
    rw [← LinearMap.toMatrix_pow, charpoly_pow_expChar,
      Polynomial.coeff_map, _root_.frobenius_def]
    conv_rhs => rw [neg_eq_zero_sub]
    rw [sub_pow_expChar, zero_pow hn.ne', zero_sub]

  theorem Algebra.trace_pow_expChar
    {S : Type*} [CommRing S] [Algebra R S]
    (x : S) :
      trace R S (x ^ n) = trace R S x ^ n := by
    rw [trace_apply, trace_apply, ← LinearMap.trace_pow_expChar, map_pow]
end trace_pow_expChar


open scoped algebraMap

section
  -- this is a simple little wrapper around zorn's lemma for
  -- building intermediate fields by adjoining elements
  open IntermediateField
  theorem IntermediateField.adjoin_simple_transfinite_induction
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    {P : IntermediateField F E → Prop} (s : Set E)
    (step : ∀ K, ∀ a ∈ s, P K → P (K⟮a⟯.restrictScalars F))
    (infty : ∀ C : Set _, IsChain (· ≤ ·) C → (∀ K ∈ C, P K) → P (sSup C)) :
      P (adjoin F s) := by
    let ok := {t ⊆ s | P (adjoin F t)}
    have ⟨t, ht⟩ : ∃ t, Maximal (· ∈ ok) t := zorn_subset ok fun c c_sub hc => by
      refine ⟨sSup c, ?_, fun z => le_sSup⟩
      refine ⟨sSup_le fun t ht => c_sub ht |>.1, ?_⟩
      convert infty
        (adjoin F '' c)
        (hc.image _ _ _ fun x y h => adjoin.mono _ _ _ h)
        fun t ⟨_, ht⟩ => ht.2 ▸ (c_sub ht.1).2
      rw [IntermediateField.gc.l_sSup, sSup_image]
    suffices t = s from this ▸ ht.prop.2
    by_contra t_lt
    apply ht.prop.1.ssubset_of_ne at t_lt
    have ⟨a, ha, hat⟩ := Set.exists_of_ssubset t_lt
    suffices t.insert a ∈ ok by
      absurd ht.not_gt this
      exact t.ssubset_insert hat
    refine ⟨t.insert_subset ha t_lt.subset, ?_⟩
    convert step _ a ha ht.prop.2
    rw [adjoin_adjoin_left, Set.union_comm]; rfl
end

namespace Construction

open Polynomial

noncomputable section defs
  def F₀ := RatFunc $ AlgebraicClosure (ZMod 2)
  instance : Field F₀ := by unfold F₀; infer_instance
  instance : CharP F₀ 2 := Algebra.charP_iff (AlgebraicClosure (ZMod 2)) (RatFunc _) _
    |>.mp inferInstance
  def F₀.T : F₀ := RatFunc.X

  def F₀.poly : F₀[X] := X ^ 2 + X + C T

  -- another choice for F which works is a maximal odd subextension of F₀
  def F' : ℕ → IntermediateField F₀ (AlgebraicClosure F₀)
    | 0 => ⊥
    | n + 1 => .restrictScalars F₀ $ .adjoin (F' n) {x | ∃ p, Odd p ∧ p.Prime ∧ x ^ p ∈ F' n}
  def F := iSup F'

  def E := AdjoinRoot (R := F) $ F₀.poly.map $ algebraMap F₀ F
  -- proving E is a field will have to wait
end defs


open Algebra IntermediateField AdjoinSimple

section first
  variable {F E : Type*} [Field F] [CharP F 2] [Field E] [Algebra F E]
    {p : ℕ} (p_odd : Odd p) [hp : Fact p.Prime]
    (h_roots : ∀ a : E, a ^ p = 1 → a ∈ (algebraMap F E).range)
    {x : E} {r : F} (hx : x ^ p = r)
  include h_roots hx

  omit [CharP F 2] in
  lemma natDegree_adjoin_simple_of_no_new_roots :
      (minpoly F x).natDegree ∣ p := by
    by_cases hx' : x ∈ (algebraMap F E).range
    . rcases hx' with ⟨x, rfl⟩
      erw [minpoly.eq_X_sub_C, natDegree_X_sub_C]
      apply one_dvd
    . suffices minpoly F x = X ^ p - C r by
        rw [this, natDegree_X_pow_sub_C]
      rw [← minpoly.eq_of_irreducible_of_monic ?hp1 ?hp2 ?hp3]
      case hp1 =>
        obtain rfl | r_nz := eq_or_ne r 0
        . simp only [map_zero, pow_eq_zero_iff', ne_eq] at hx
          simp [hx.1, zero_mem] at hx'
        apply X_pow_sub_C_irreducible_of_prime hp.1
        intro b
        contrapose! hx' with hb
        have b_nz : b ≠ 0 := by
          rintro rfl
          rw [zero_pow hp.1.ne_zero] at hb
          exact r_nz hb.symm
        rw [← hb] at hx
        push_cast at hx
        rw [← div_eq_one_iff_eq (by rw_mod_cast [hb]; exact r_nz), ← div_pow] at hx
        apply h_roots _ at hx
        rcases hx with ⟨v, hv⟩
        exists v * b
        rw [map_mul, hv, div_mul_cancel₀]
        exact_mod_cast b_nz
      case hp2 =>
        simp only [map_sub, map_pow, aeval_X, hx, aeval_C]
        rw [sub_eq_zero]
      case hp3 =>
        apply monic_X_pow_sub_C _ hp.1.ne_zero

  include p_odd in
  lemma adjoin_simple_step_down
    (k : F) (h : ∃ b ∈ (IntermediateField.adjoin F {x}), b ^ 2 + b + k = 0) :
      ∃ a : F, a ^ 2 + a + k = 0 := by
    rcases h with ⟨b, b_mem, hb⟩
    lift b to F⟮x⟯ using b_mem
    rw [show b.val = b from rfl, show (k : E) = (k : F⟮x⟯) by simp] at hb
    norm_cast at hb
    exists trace F _ b
    norm_cast
    rw [← trace_pow_expChar]
    suffices k = trace F F⟮x⟯ k by
      rw [this]
      simp_rw [← map_add, hb, map_zero]
    simp only [trace_algebraMap, nsmul_eq_mul]
    obtain ⟨u, hu⟩ : Odd (minpoly F x).natDegree := p_odd.of_dvd_nat $
      natDegree_adjoin_simple_of_no_new_roots h_roots hx
    rw [adjoin.finrank (.of_pow hp.1.pos $ hx ▸ isIntegral_algebraMap), hu]
    simp [CharTwo.two_eq_zero]
end first


section induction

private lemma AlgClosed_has_nth_roots
  (F : Type*) [Field F] [IsAlgClosed F]
  {E : Type*} [Field E] [Algebra F E]
  {n : ℕ} (hn : 0 < n) :
    ∀ a : E, a ^ n = 1 → a ∈ (⊥ : IntermediateField F E) := by
  intro a ha
  let p : F[X] := X ^ n - C 1
  replace ha : a ∈ p.aroots E := by
    suffices ¬ (X ^ n - C 1 : E[X]) = 0 by simpa [p, ha]
    apply Polynomial.X_pow_sub_C_ne_zero hn
  have : p.aroots E = _ := Polynomial.roots_map (algebraMap F E) $ IsAlgClosed.splits p
  rw [this, Multiset.mem_map] at ha
  rcases ha with ⟨b, _, rfl⟩
  simp [IntermediateField.mem_bot]

private lemma F₀_has_nth_roots {E : Type*} [Field E] [Algebra F₀ E] {n : ℕ} (hn : 0 < n) :
    ∀ a : E, a ^ n = 1 → a ∈ (⊥ : IntermediateField F₀ E) := by
  let F2bar := AlgebraicClosure (ZMod 2)
  letI : Algebra F2bar F₀ := RatFunc.instAlgebraOfPolynomial ..
  letI : Algebra F2bar E := (algebraMap F₀ E).comp (algebraMap F2bar F₀) |>.toAlgebra
  intro a ha
  have h := AlgClosed_has_nth_roots F2bar hn a ha
  rw [IntermediateField.mem_bot] at h ⊢
  rcases h with ⟨b, rfl⟩
  exists b


lemma F₀.poly_deg : degree poly = 2 := by
  rw [poly, add_assoc, degree_add_eq_left_of_degree_lt] <;> simp

lemma F₀.poly_Monic : Monic poly := by
  rw [F₀.poly, add_assoc]
  apply Monic.add_of_left <;> simp


private abbrev not_a_root {E : Type*} [Field E] [Algebra F₀ E] (x : E) :=
  x^2 + x + F₀.T ≠ 0

lemma not_a_root_iff {E : Type*} [Field E] [Algebra F₀ E] (x : E) :
    not_a_root x ↔ ¬ aeval x F₀.poly = 0 := by
  simp [not_a_root, F₀.poly]


lemma F₀.no_roots.aux {F : Type*} [Field F] (p : F[X]) :
    p ^ 2 + p + X ≠ 0 := by
  rw [ne_eq, ← eq_sub_iff_add_eq, zero_sub]
  apply mt (congrArg natDegree)
  rw [natDegree_neg, natDegree_X]
  have := p.natDegree_pow 2
  have := natDegree_add_le (p ^ 2) p
  by_cases hd : p.natDegree = 0
  . omega
  . rw [natDegree_add_eq_left_of_natDegree_lt] <;> omega

open RatFunc hiding X C in
lemma F₀.no_roots : ∀ x : F₀, not_a_root x := by
  let F := AlgebraicClosure (ZMod 2)
  convert_to ∀ x : RatFunc F, not_a_root x

  simp_rw [not_a_root_iff]
  intro x hx

  let p : (RatFunc F)[X] := X ^ 2 + X + C RatFunc.X
  let p' : F[X][Y] := Y ^ 2 + Y + C X
  have hp : p = p'.map (algebraMap _ _) := by simp [p, p']
  have p'_monic : Monic p' := by
    simp only [p', add_assoc]; apply Monic.add_of_left <;> simp

  replace hx : aeval x p = 0 := hx
  rw [hp, aeval_map_algebraMap] at hx
  obtain ⟨x, rfl⟩ := isInteger_of_is_root_of_monic p'_monic hx
  apply isRoot_of_aeval_algebraMap_eq_zero (algebraMap_injective _) at hx
  apply no_roots.aux x; simpa [p'] using hx

lemma F'.no_roots.base : ∀ x ∈ F' 0, not_a_root x := by
  intro x hx
  rw [F'] at hx
  lift x to (⊥ : IntermediateField F₀ (AlgebraicClosure F₀)) using hx
  show not_a_root (x : AlgebraicClosure F₀)
  rw [not_a_root_iff, aeval_algebraMap_eq_zero_iff,
    ← aeval_algebraMap_eq_zero_iff F₀, ← not_a_root_iff]
  apply F₀.no_roots

lemma F'.no_roots n : ∀ x ∈ F' n, not_a_root x := by
  induction n with
  | zero => apply F'.no_roots.base
  | succ n ih =>
    simp_rw [F', mem_restrictScalars]
    apply IntermediateField.adjoin_simple_transfinite_induction (P := fun K => ∀ x ∈ K, not_a_root x)
    case infty =>
      intro c hc h x hx
      obtain rfl | c_ne := c.eq_empty_or_nonempty
      . apply ih; simpa [IntermediateField.mem_bot] using hx
      haveI : Nonempty c := c_ne.to_subtype
      rw [← SetLike.mem_coe, sSup_eq_iSup', coe_iSup_of_directed hc.directed,
        Set.mem_iUnion] at hx
      rcases hx with ⟨i, hx⟩
      exact h _ i.2 _ hx
    rintro K a ⟨p, p_odd, hp, ha⟩ ihK
    haveI : Fact p.Prime := ⟨hp⟩
    simp_rw [mem_restrictScalars]
    contrapose! ihK with hKa
    simp_rw [ne_eq, not_not, show (F₀.T : AlgebraicClosure F₀) = ((F₀.T : F' n) : K) by simp] at hKa ⊢
    generalize hr : a ^ p = r
    lift r to F' n using hr ▸ ha
    replace hr : a ^ p = (r : K) := by exact_mod_cast hr
    suffices ∃ x : K, x ^ 2 + x + F₀.T = 0 by
      rcases this with ⟨x, hx⟩
      exists x, by simp only [IntermediateField.algebraMap_apply, SetLike.coe_mem]
      exact_mod_cast hx
    apply adjoin_simple_step_down p_odd ?_ hr _ hKa
    intro a ha
    have := F₀_has_nth_roots hp.pos a ha
    rw [IntermediateField.mem_bot] at this
    rcases this with ⟨b, rfl⟩
    exists b

lemma F'.monotone : Monotone F' := by
  apply monotone_nat_of_le_succ
  intro n
  rw [← IntermediateField.adjoin_self F₀ (F' n), F', IntermediateField.restrictScalars_adjoin]
  apply IntermediateField.adjoin.mono
  simp

lemma F.mem_iff x : x ∈ F ↔ ∃ n, x ∈ F' n := by
  rw [F, ← SetLike.mem_coe, coe_iSup_of_directed F'.monotone.directed_le]
  simp

lemma F.no_roots : ∀ x ∈ F, not_a_root x := by
  intro x hx
  rw [F.mem_iff] at hx
  rcases hx with ⟨i, h⟩
  exact F'.no_roots i x h

lemma F.irred : Irreducible (F₀.poly.map (algebraMap F₀ F)) := by
  have p_deg : degree F₀.poly = 2 := F₀.poly_deg
  have p_natDeg : natDegree F₀.poly = 2 := natDegree_eq_of_degree_eq_some p_deg

  rw [irreducible_iff_lt_natDegree_lt]
  case hp0 =>
    rw [ne_eq, Polynomial.map_eq_zero, ← degree_eq_bot, p_deg]
    decide
  case hpu =>
    apply not_isUnit_of_degree_pos_of_isReduced
    rw [degree_map, p_deg]
    decide
  intro q q_monic q_natDeg
  replace q_natDeg : q.natDegree = 1 := by simpa [p_natDeg] using q_natDeg
  rw [natDegree_eq_one] at q_natDeg
  rcases q_natDeg with ⟨a, ha, b, rfl⟩
  let c := -b / a
  have h : X - C c ∣ C a * X + C b := by
    apply dvd_of_mul_left_eq (C a)
    dsimp only [c]
    rw [sub_eq_add_neg, ← C_neg, mul_add, ← C_mul]
    congr
    field_simp
  apply mt h.trans
  rw [dvd_iff_isRoot]
  have := F.no_roots c c.2
  rw [not_a_root, show (F₀.T : AlgebraicClosure F₀) = (F₀.T : F) by simp] at this
  norm_cast at this
  simpa [F₀.poly]

lemma F.odd_prime_radically_closed.aux
  {p : ℕ} (p_odd : Odd p) (hp : p.Prime)
  {x : AlgebraicClosure F₀} (hx : x ^ p ∈ F) :
    x ∈ F := by
  rw [mem_iff] at hx ⊢
  rcases hx with ⟨n, hn⟩
  exists n + 1
  rw [F', mem_restrictScalars]
  apply IntermediateField.subset_adjoin
  exists p

lemma F.odd_prime_radically_closed
  {E : Type*} [Field E] [Algebra F E]
  {p : ℕ} (p_odd : Odd p) (hp : p.Prime)
  {x : E} (hx : x ^ p ∈ (algebraMap F E).range) :
    x ∈ (algebraMap F E).range := by
  rcases hx with ⟨y, hy⟩
  have xp_int : IsIntegral F (x ^ p) := hy ▸ isIntegral_algebraMap
  have x_int : IsIntegral F x := xp_int.of_pow hp.pos

  -- transport to F⟮x⟯
  letI : Algebra F F⟮x⟯ := Subalgebra.algebra _
  rw [← coe_gen F x] at hy ⊢
  set x' : F⟮x⟯ := gen F x
  change ((y : F⟮x⟯) : E) = x' ^ p at hy
  norm_cast at hy
  suffices x' ∈ (algebraMap F F⟮x⟯).range by
    clear_value x'
    rcases this with ⟨y, rfl⟩
    exists y

  -- transport to AlgebraicClosure F₀
  letI : Algebra F₀ F⟮x⟯ := (algebraMap F F⟮x⟯).comp (algebraMap F₀ F) |>.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq (R := F₀) (S := F) (A := F⟮x⟯) fun _ => rfl
  -- bleh why is there no applicable lemma for this
  haveI : Algebra.IsAlgebraic F₀ F := Algebra.isAlgebraic_def.mpr fun x => by
    rw [IntermediateField.isAlgebraic_iff]
    apply IsAlgClosure.algebraic.isAlgebraic
  haveI : Algebra.IsAlgebraic F F⟮x⟯ := isAlgebraic_adjoin fun x => by
    rw [Set.mem_singleton_iff]
    exact fun hx => hx ▸ x_int
  have f := IsAlgClosed.lift (R := F) (S := F⟮x⟯) (M := AlgebraicClosure F₀)

  have f_map_mem_iff {a : F⟮x⟯} : f a ∈ F ↔ a ∈ (algebraMap F F⟮x⟯).range := by
    constructor
    . intro h
      exists ⟨f a, h⟩
      rw [← (show Function.Injective f from f.injective).eq_iff]
      simp
    . rintro ⟨b, rfl⟩
      simp only [f.commutes, IntermediateField.algebraMap_apply, SetLike.coe_mem]

  apply congrArg f at hy
  rw [map_pow] at hy
  have almost := odd_prime_radically_closed.aux p_odd hp (x := f x') $ by
    rw [← hy, f_map_mem_iff]
    simp only [RingHom.mem_range, algebraMap.coe_inj, exists_eq]
  rw [f_map_mem_iff] at almost
  convert almost

end induction


instance E.instIrred : Fact (Irreducible (F₀.poly.map (algebraMap F₀ F))) :=
  ⟨F.irred⟩
noncomputable instance : Field E := by unfold E; infer_instance
noncomputable instance : Algebra F E := by unfold E; infer_instance
noncomputable instance : Algebra F₀ E := by unfold E; infer_instance
instance : IsScalarTower F₀ F E := .of_algebraMap_eq fun _ => rfl
instance : CharP E 2 := by rw [← Algebra.charP_iff F E]; infer_instance

noncomputable abbrev E.power_basis : PowerBasis F E :=
  AdjoinRoot.powerBasis $ by simp [← degree_eq_bot, F₀.poly_deg]

lemma E.pb_dim : E.power_basis.dim = 2 := by
  rw [AdjoinRoot.powerBasis_dim, natDegree_map]
  apply natDegree_eq_of_degree_eq_some $ F₀.poly_deg

theorem E.no_new_radicals
  {n : ℕ} (hn : 0 < n)
  (x : E) (hx : x ^ n ∈ (algebraMap F E).range) :
    x ∈ (algebraMap F E).range := by
  induction n using induction_on_primes with
  | h₀ => simp at hn
  | h₁ => rwa [pow_one] at hx
  | h p n hp ih =>
    specialize ih (Nat.pos_of_mul_pos_left hn); clear hn
    apply ih; clear ih
    rw [pow_mul'] at hx
    set x' := x ^ n; clear_value x'; clear x; rename' x' => x
    obtain rfl | p_odd := hp.eq_two_or_odd'
    case inr => exact F.odd_prime_radically_closed (E := E) p_odd hp hx
    rcases hx with ⟨y, hy⟩
    let pb : PowerBasis F E := E.power_basis
    have hd : pb.dim = 2 := E.pb_dim
    have ⟨f, f_deg, hx⟩ := pb.exists_eq_aeval x
    obtain ⟨a, b, rfl⟩ := f.exists_eq_X_add_C_of_natDegree_le_one (by omega)
    replace hx : x = a * pb.gen + b := by
      rwa [aeval_add, aeval_mul, aeval_C, aeval_X, aeval_C] at hx
    subst hx
    by_cases ha : a = 0
    . simp only [ha, map_zero, zero_mul, zero_add]
      exists b
    exfalso
    rw [add_pow_expChar, mul_pow] at hy
    replace hy : pb.gen ^ 2 = ((y - b ^ 2) / a ^ 2 : F) := by
      replace ha : (a : E) ≠ 0 := by exact_mod_cast ha
      push_cast; field_simp; linear_combination -hy
    have hg := minpoly.aeval F pb.gen
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic (F₀.poly_Monic.map _)] at hg
    simp_rw [aeval_map_algebraMap, F₀.poly, map_add, map_pow, aeval_X, aeval_C] at hg
    rw [add_assoc, ← CharTwo.sub_eq_add, sub_eq_zero] at hg
    rw [hg, show (algebraMap F₀ E F₀.T) = (F₀.T : F) by rfl,
      ← CharTwo.sub_eq_add, sub_eq_iff_eq_add] at hy
    norm_cast at hy
    -- i feel like there's a better way to finish, but this is passable
    absurd minpoly.degree_eq_one_iff.mpr ⟨_, hy.symm⟩
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic (F₀.poly_Monic.map _),
      degree_map, F₀.poly_deg]
    decide

end Construction


section finale

class inductive IsSimpleRadicalExtension
    (R A : Type*) [Field R] [Field A] [Algebra R A] : Prop where
  | exists_gen (α : A) (n : ℕ+)
      (gen_pow_mem : α ^ (n : ℕ) ∈ Set.range (algebraMap R A))
      (adjoin_gen : IntermediateField.adjoin R {α} = ⊤)

structure Construction.Finale where
  (F : Type*) [hF : Field F]
  (E : Type*) [hE : Field E] [hFE : Algebra F E]
  quadratic : Module.finrank F E = 2
  not_radical : ¬ IsSimpleRadicalExtension F E

open IntermediateField in
noncomputable def Construction.quadratic_and_not_radical_field_extension :
    Construction.Finale where
  F := F
  E := E
  quadratic := by rw [E.power_basis.finrank, E.pb_dim]
  not_radical := by
    rintro ⟨α, n, hα, h⟩
    apply E.no_new_radicals n.2 _ at hα
    rw [adjoin_simple_eq_bot_iff.mpr (mem_bot.mpr hα)] at h
    absurd IntermediateField.finrank_bot (F := F) (E := E)
    rw [h, finrank_top', E.power_basis.finrank, E.pb_dim]
    decide

end finale
