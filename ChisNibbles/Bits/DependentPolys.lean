import Mathlib

/-
n + 1 polynomials in R[x1, …, xn] are algebraically dependent over R.
-/


/-
easy proof for a domain using transcendence degree
-/
theorem dependent_polys_of_isDomain
  (R : Type*) [CommRing R] [IsDomain R]
  (n : ℕ) (p : Fin (n + 1) → MvPolynomial (Fin n) R) :
    ¬ AlgebraicIndependent R p :=
  fun hp => absurd hp.lift_cardinalMk_le_trdeg <| by simp; norm_cast; omega



namespace MvPolynomial
  variable {R σ : Type*} [CommRing R] (I : Ideal R) (f : MvPolynomial σ R)
  open Ideal.Quotient

  @[simp]
  theorem quotientEquivQuotientMvPolynomial_symm_mk :
      (quotientEquivQuotientMvPolynomial I).symm (mk _ f) = map (mk _) f := by
    simp [quotientEquivQuotientMvPolynomial, ← bind₂_map]

  @[simp]
  theorem quotientEquivQuotientMvPolynomial_map_mk :
      quotientEquivQuotientMvPolynomial I (map (mk _) f) = mk _ f := by
    apply quotientEquivQuotientMvPolynomial I |>.symm.injective
    simp
end MvPolynomial


theorem iUnion_minimalPrimes_of_isReduced
  (R : Type*) [CommRing R] [IsReduced R] :
    ⋃ p ∈ minimalPrimes R, p = (nonZeroDivisors R : Set R)ᶜ := by
  apply subset_antisymm
  . rw [Set.subset_compl_iff_disjoint_right]
    simp +contextual [Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes]
  erw [Ideal.iUnion_minimalPrimes]
  intro x
  simp only [Set.mem_compl_iff, SetLike.mem_coe, notMem_nonZeroDivisors_iff_right, ne_eq,
    Set.nonempty_def, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro y hx hy
  exact ⟨y, by erw [mem_nilradical]; simpa, by rw [mul_comm, hx]; simp⟩

theorem isArtinianRing_of_isReduced_of_isNoetherian_of_forall_nonZeroDivisor_isUnit
  (R : Type*) [CommRing R] [IsReduced R] [IsNoetherianRing R]
  (h : ∀ r ∈ nonZeroDivisors R, IsUnit r) :
    IsArtinianRing R := by
  nontriviality R
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_iff, ringKrullDim_le_iff_height_le]
  intro p hp
  norm_cast
  rw [nonpos_iff_eq_zero, p.height_eq_primeHeight, p.primeHeight_eq_zero_iff]
  suffices ∃ q ∈ minimalPrimes R, p ≤ q by
    simp_rw [minimalPrimes_eq_minimals, Set.mem_setOf_eq] at this ⊢
    rcases this with ⟨q, hq, hp⟩
    exact hq.eq_of_le ‹_› hp ▸ hq
  have ⟨r⟩ : Nonempty (minimalPrimes R) := Ideal.nonempty_minimalPrimes bot_ne_top
  rw [← Ideal.subset_union_prime_finite (minimalPrimes.finite_of_isNoetherianRing R)
      r r (fun _ h _ _ => Ideal.minimalPrimes_isPrime h),
    iUnion_minimalPrimes_of_isReduced, Set.subset_compl_iff_disjoint_right, Set.disjoint_iff]
  exact fun x ⟨h₁, h₂⟩ => hp.ne_top <| p.eq_top_of_isUnit_mem h₁ (h _ h₂)

theorem isArtinianRing_of_isFractionRing_of_reduced_noetherian
  (R : Type*) [CommRing R] [IsReduced R] [IsNoetherianRing R]
  (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K] :
    IsArtinianRing K :=
  -- why are there universe issues here rip
  -- and TODO these instances should probably get pulled out
  have : IsReduced K := isReduced_of_injective (FractionRing.algEquiv R K).symm (AlgEquiv.injective _)
  have : IsNoetherianRing K := IsLocalization.isNoetherianRing (nonZeroDivisors R) _ ‹_›
  isArtinianRing_of_isReduced_of_isNoetherian_of_forall_nonZeroDivisor_isUnit K fun r hr => by
    have ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) r
    lift a to nonZeroDivisors R
    . -- TODO could also pull out nonZeroDivisors R = comap nonZeroDivisors M^-1 R
      -- as long as M ≤ nonZeroDivisors R (and the corresponding iff)
      apply mem_nonZeroDivisors_of_injective (IsFractionRing.injective R K)
      rw [← h, mul_mem_nonZeroDivisors]
      exact ⟨hr, IsLocalization.map_nonZeroDivisors_le (nonZeroDivisors R) K (by simp)⟩
    exact isUnit_of_mul_isUnit_left (h ▸ IsLocalization.map_units K a)

instance instIsArtinianRingFractionRingOfReducedNoetherian
  (R : Type*) [CommRing R] [IsReduced R] [IsNoetherianRing R] :
    IsArtinianRing (FractionRing R) :=
  isArtinianRing_of_isFractionRing_of_reduced_noetherian R _



theorem Algebra.TensorProduct.map_toLinearMap_restrictScalars
  {R S A B C D : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Semiring B] [Algebra R B]
  [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C] [Semiring D] [Algebra R D]
  (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g).toLinearMap = _root_.TensorProduct.map (f.toLinearMap.restrictScalars R) g.toLinearMap := by
  ext; simp


-- kinda funny that RingEquiv doesnt have a constructor that takes
-- → hom and ← fun because that's more or less literally the definition
-- (there is RingHom.inverse which is something I guess)
@[simps! apply]
noncomputable def MvPolynomial.piEquiv
  (σ : Type*) {ι : Type*} [Finite ι] (R : ι → Type*) [∀ i, CommSemiring (R i)] :
    MvPolynomial σ (∀ i, R i) ≃+* ∀ i, MvPolynomial σ (R i) :=
  .ofBijective (Pi.ringHom fun i => map (Pi.evalRingHom R i)) <| by
    constructor
    . intro p q h; ext n i; simpa [coeff_map] using congr(coeff n ($h i))
    . intro p
      let q := Finsupp.ofSupportFinite (fun n i => coeff n (p i)) <| by
        apply Set.finite_iUnion (fun i => (p i).support.finite_toSet) |>.subset
        simp only [Function.support_subset_iff, ne_eq, Set.mem_iUnion, Finset.mem_coe,
          mem_support_iff]
        intro x; contrapose!; aesop
      exists q
      ext i n; apply coeff_map


theorem MvPolynomial.aeval_pi
  {R σ : Type*} [CommSemiring R]
  {I : Type*} {A : I → Type*} [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)]
  (f : σ → ∀ i, A i) :
    aeval f = Pi.algHom R A (fun i => aeval (f · i)) := by
  convert Pi.algHom_comp R A (Pi.evalAlgHom R A) (aeval f) with i
  ext x; simp

-- idk wtf to call this
-- also RHS can also be written `Pi.ringHom (fun i => aeval (f · i) |>.toRingHom.comp <| map (Pi.evalRingHom R i))`,
-- but this version is more convenient
theorem MvPolynomial.aeval_pi_over_pi
  {σ I : Type*} [Finite I] {R : I → Type*} [∀ i, CommSemiring (R i)]
  {A : I → Type*} [∀ i, CommSemiring (A i)] [∀ i, Algebra (R i) (A i)]
  (f : σ → ∀ i, A i) :
    (aeval f).toRingHom =
      (Pi.ringHom (fun i => aeval (f · i) |>.toRingHom.comp <| Pi.evalRingHom _ i)).comp (piEquiv σ R).toRingHom := by
  ext x i <;> simp [algebraMap, Pi.instAlgebraForall]


/-
... and with some fun commutative algebra we can transport to any (nontrivial) comm ring!
-/
attribute [local instance] MvPolynomial.algebraMvPolynomial IsArtinianRing.fieldOfSubtypeIsMaximal in
open MvPolynomial Ideal.Quotient in
open Ideal hiding map in
open scoped TensorProduct in
example
  (R : Type*) [CommRing R] [Nontrivial R]
  (n : ℕ) (p : Fin (n + 1) → MvPolynomial (Fin n) R) :
    ¬ AlgebraicIndependent R p := by
  intro hp

  wlog _ : IsNoetherianRing R
  . letI S : Subring R := .closure (⋃ i, (p i).coeffs)
    have _ : IsNoetherianRing S := is_noetherian_subring_closure _ (by simp [Set.finite_iUnion])
    have h i : p i ∈ Set.range (map S.subtype) := by
      grw [mem_range_map_iff_coeffs_subset, Subring.coe_subtype, Subtype.range_coe_subtype,
        SetLike.setOf_mem_eq, ← Subring.subset_closure, ← Set.subset_iUnion]
    simp_rw [Set.mem_range] at h
    choose q hq using h
    rw [← funext (g := p) hq] at hp
    have hq : AlgebraicIndependent S q :=
      hp.of_ringHom_of_comp_eq (hf := S.subtype_injective) (h := by ext; simp)
    exact this S _ q hq ‹_›

  wlog _ : IsReduced R
  . letI A := R ⧸ nilradical R
    have _ : IsReduced A := isRadical_iff_quotient_reduced _ |>.mp <| radical_isRadical _
    have _ : Nontrivial A := Ideal.Quotient.nontrivial (by simp [nilradical, radical_eq_top])
    letI q : _ → MvPolynomial (Fin n) A := algebraMap _ _ ∘ p
    specialize this A _ q <| show AlgebraicIndependent A q by
      -- TODO kinda jank
      rw [algebraicIndependent_iff] at hp ⊢
      intro f hf
      rcases map_surjective _ mk_surjective f with ⟨f, rfl⟩
      erw [aeval_map_algebraMap, aeval_algebraMap_apply, ← (quotientEquivQuotientMvPolynomial _).map_eq_zero_iff,
        quotientEquivQuotientMvPolynomial_map_mk, eq_zero_iff_mem] at hf
      grw [nilradical, map_radical_le] at hf
      erw [Ideal.map_bot, mem_nilradical] at hf
      rcases hf with ⟨m, hf⟩
      apply IsReduced.pow_eq_zero (n := m)
      rw [← map_pow] at hf ⊢
      convert RingHom.map_zero _
      exact hp _ hf
    apply this <;> infer_instance

  wlog _ : IsArtinianRing R
  . letI K := FractionRing R
    letI q : _ → MvPolynomial (Fin n) K := algebraMap _ _ ∘ p
    specialize this K _ q <| show AlgebraicIndependent K q by
      -- TODO surely this can also be optimised, there's a whole lot of proving not much
      rw [algebraicIndependent_iff_injective_aeval] at hp ⊢
      letI f := Algebra.TensorProduct.map (AlgHom.id K K) (aeval (R := R) p)
      have hf : Function.Injective f := by
        change Function.Injective (f.toLinearMap.restrictScalars R)
        rw [Algebra.TensorProduct.map_toLinearMap_restrictScalars]
        apply TensorProduct.map_injective_of_flat_flat
        . simp [Function.injective_id]
        . exact hp
      letI e {σ} := algebraTensorAlgEquiv (σ := σ) R K
      rw [← e.symm.injective_comp, ← e.comp_injective] at hf
      convert hf
      erw [← Function.comp_assoc, e.eq_comp_symm]
      change aeval q ∘ e.toAlgHom = e.toAlgHom ∘ f
      rw [← AlgHom.coe_comp, ← AlgHom.coe_comp, AlgHom.coe_fn_inj]
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [f, q, e, map_bind₁, Function.comp_def]
    apply this <;> infer_instance

  have e := IsArtinianRing.equivPi R
  letI p' := (mapEquiv _ e |>.trans <| piEquiv _ _) ∘ p
  have hp' : AlgebraicIndependent (∀ I : MaximalSpectrum R, R ⧸ I.asIdeal) p' :=
    (·.mpr hp) <| algebraicIndependent_ringHom_iff_of_comp_eq
      (f := e) (hg := RingEquiv.injective _) (h := by
        ext x I : 2
        simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
          RingEquiv.coe_ringHom_trans, MvPolynomial.algebraMap_eq, mapEquiv_apply,
          piEquiv_apply, Pi.evalRingHom_apply, map_C]
        rfl)
  clear_value p'; clear e p hp; rename' p' => p, hp' => hp

  -- and finally reduce to the domain case
  -- just using elements, because it kind of sucks to do otherwise
  have yay i := dependent_polys_of_isDomain _ _ (p · i)
  revert hp
  simp only [algebraicIndependent_iff, imp_false] at yay ⊢
  push_neg at yay ⊢
  choose q hq q_nz using yay
  refine ⟨(piEquiv _ _).symm q, ?_, ?_⟩
  . change (aeval p).toRingHom _ = 0
    rw [aeval_pi_over_pi]
    ext i : 1
    simpa using hq i
  . suffices q ≠ 0 by simpa
    intro h
    simp [h] at q_nz





/-
the original proof: we can directly prove for any comm ring by counting
-/
open List in
@[simp] theorem List.Nat.length_antidiagonalTuple : ∀ k n, length (antidiagonalTuple k n) = (n + k - 1).choose n
  | 0, 0     => rfl
  | 0, n + 1
  | 1, n     => by simp
  | k + 2, n => by
    rw [antidiagonalTuple]
    simp only [length_antidiagonalTuple, length_map, length_flatMap,
      Nat.add_succ_sub_one, Nat.choose_symm_add]
    simp_rw [Nat.add_comm _ k]
    rw [Nat.choose_symm_add]
    rw [show n + (k + 1) = k + n + 1 by abel, ← Finset.sum_antidiagonal_choose_add]
    rw [← (antidiagonal n).sum_toFinset _ (nodup_antidiagonal n)]
    congr; ext; simp

open Multiset in
@[simp] theorem Multiset.Nat.card_antidiagonalTuple k n : card (antidiagonalTuple k n) = (n + k - 1).choose n :=
  List.Nat.length_antidiagonalTuple ..

open Finset in
@[simp] theorem Finset.Nat.card_antidiagonalTuple k n : #(antidiagonalTuple k n) = (n + k - 1).choose n :=
  Multiset.Nat.card_antidiagonalTuple ..


lemma Finset.finAntidiagonal_eq_antidiagonalTuple (n k : ℕ) :
    finAntidiagonal k n = Nat.antidiagonalTuple k n := by
  ext; simp [Nat.mem_antidiagonalTuple]

open Finset in
@[simp] theorem Finset.card_finAntidiagonal_nat (d n : ℕ) :
    #(finAntidiagonal d n) = (n + d - 1).choose n := by
  simp [Finset.finAntidiagonal_eq_antidiagonalTuple]

open Finset in
@[simp] theorem Finset.card_piAntidiag_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (n : ℕ) :
    #(piAntidiag s n) = (n + #s - 1).choose n := by
  rw [piAntidiag]
  induction Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s using Trunc.ind with | _ e =>
  simp [Trunc.lift_mk, card_map]


open Finset in
theorem Finset.card_finsuppAntidiag_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (n : ℕ) :
    #(finsuppAntidiag s n) = (n + #s - 1).choose n := by
  rw [finsuppAntidiag, card_map, card_attach, card_piAntidiag_nat]


open Finset Module in
theorem MvPolynomial.finrank_restrictTotalDegree
  {σ : Type*} (R : Type*) [CommSemiring R] [StrongRankCondition R] [Fintype σ] (m : ℕ) :
    Module.finrank R (restrictTotalDegree σ R m) = (m + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  -- TODO: should this be a separate lemma?
  let s : Finset (σ →₀ ℕ) := range (m + 1) |>.disjiUnion univ.finsuppAntidiag <| by
    letI sm : (σ →₀ ℕ) → ℕ := (univ.sum ·)
    have h i : image sm (univ.finsuppAntidiag i) ⊆ {i} := by intro a; aesop
    intro i _ j _ hij
    apply Disjoint.of_image_finset ∘ Disjoint.mono (h i) (h j)
    aesop
  let b : Basis s R (restrictTotalDegree σ R m) := basisRestrictSupport _ _ |>.reindex <| by
    apply Equiv.setCongr
    ext n; dsimp
    show _ ↔ n ∈ s
    simp only [disjiUnion_eq_biUnion, mem_biUnion, mem_range, Nat.lt_succ_iff, mem_finsuppAntidiag',
      subset_univ, and_true, exists_eq_right', s]
  rw [Module.finrank_eq_card_finset_basis b]
  rw [card_disjiUnion]
  simp_rw [card_finsuppAntidiag_nat, card_univ]
  obtain hσ | hσ := (Fintype.card σ).eq_zero_or_pos
  . rw [sum_range_succ']
    simp [hσ]
  conv_lhs => arg 2; ext; rw [Nat.add_sub_assoc hσ.nat_succ_le, Nat.choose_symm_add]
  rw [Nat.sum_range_add_choose]
  congr 1 <;> omega

theorem LinearMap.injective_restrict_of_injective
  {R M M₁ : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]
  {f : M →ₗ[R] M₁} (f_inj : Function.Injective f)
  {p : Submodule R M} {q : Submodule R M₁}
  (hf : ∀ x ∈ p, f x ∈ q) :
    Function.Injective (restrict f hf) :=
  fun _ _ h => Subtype.ext <| f_inj congr($h.1)

theorem AlgebraicIndependent.injective_aeval
  {ι R A : Type*} {x : ι → A} [CommRing R] [CommRing A] [Algebra R A]
  (h : AlgebraicIndependent R x) :
    Function.Injective (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A) :=
  h


namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable {S : Type*} [NormedRing S] [NormMulClass S]
variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variable {l l' : Filter α}

open Filter

theorem IsTheta.comp_tendsto (hfg : f =Θ[l] g) {k : β → α} {l' : Filter β} (hk : Filter.Tendsto k l' l) :
    (f ∘ k) =Θ[l'] (g ∘ k) :=
  ⟨hfg.isBigO.comp_tendsto hk, hfg.isBigO_symm.comp_tendsto hk⟩

end Asymptotics


open MvPolynomial Filter

theorem dependent_polys
  (R : Type*) [CommRing R] [Nontrivial R]
  (n : ℕ) (p : Fin (n + 1) → MvPolynomial (Fin n) R) :
    ¬ AlgebraicIndependent R p := by
  intro hp

  -- d is a strict upper bound on the degrees
  let d := Finset.univ.image (totalDegree ∘ p) |>.max' (by simp) |>.succ
  have d_pos : 0 < d := by simp [d]
  have hd {i} : (p i).totalDegree < d := by simp [d, Nat.lt_succ_iff, Finset.le_max']
  clear_value d

  let f k : restrictTotalDegree (Fin (n + 1)) R (k / d) →ₗ[R] restrictTotalDegree (Fin n) R k :=
    aeval p |>.toLinearMap.restrict fun q hq => by
      rw [mem_restrictTotalDegree] at hq ⊢
      rw [q.as_sum]
      simp_rw [AlgHom.toLinearMap_apply, aeval_sum, aeval_monomial]
      simp_rw [algebraMap_eq, ← smul_eq_C_mul, Finsupp.prod_pow]
      apply totalDegree_finsetSum_le
      intro s hs
      have h : s.sum (fun _ e => e) = ∑ i, s i := Fintype.sum_subset (by simp)
      grw [totalDegree_smul_le, totalDegree_finset_prod,
        Finset.sum_le_sum (fun _ _ => totalDegree_pow ..),
        Finset.sum_le_sum (fun _ _ => Nat.mul_le_mul_left _ hd.le),
        ← Finset.sum_mul, Nat.mul_le_mul_right _ (h ▸ le_totalDegree hs),
        Nat.mul_le_mul_right _ hq, Nat.div_mul_le_self]
  have f_inj k : Function.Injective (f k) :=
    LinearMap.injective_restrict_of_injective hp.injective_aeval _

  have h k := (f k).finrank_le_finrank_of_injective (f_inj k)
  simp only [finrank_restrictTotalDegree, Fintype.card_fin] at h
  clear * - d_pos h

  suffices (· ^ (n + 1) : ℕ → ℝ) =O[.atTop] (· ^ n : ℕ → ℝ) by
    apply this.not_isLittleO
    . simp [frequently_atTop]; intro a; exists a + 1; simp
    . exact Asymptotics.isLittleO_pow_pow_atTop_of_lt n.lt_succ_self
        |>.comp_tendsto tendsto_natCast_atTop_atTop

  rify at h
  replace h :
      (fun k => (k / d + (n + 1)).choose (n + 1) : ℕ → ℝ) =O[.atTop]
      (fun k => (k + n).choose n : ℕ → ℝ) :=
    Asymptotics.IsBigO.of_norm_le fun k => Real.norm_natCast _ |>.trans_le <| h k
  calc
    (· ^ (n + 1) : ℕ → ℝ) =O[.atTop] (fun k => (k / d + (n + 1) : ℕ) ^ (n + 1) : ℕ → ℝ)
      := .pow ?_ _
    _                      =Θ[.atTop] (fun k => (k / d + (n + 1)).choose (n + 1) : ℕ → ℝ)
      := isTheta_choose _ |>.symm.comp_tendsto <|
           tendsto_add_atTop_nat _ |>.comp <| Nat.tendsto_div_const_atTop d_pos.ne'
    _                      =O[.atTop] (fun k => (k + n).choose n : ℕ → ℝ)
      := h
    _                      =Θ[.atTop] (fun k => (k + n : ℕ) ^ n : ℕ → ℝ)
      := isTheta_choose n |>.comp_tendsto <| tendsto_add_atTop_nat _
    _                      =O[.atTop] (· ^ n : ℕ → ℝ)
      := .pow ?_ _
  . apply Asymptotics.IsBigO.of_bound d
    filter_upwards with a
    norm_cast
    apply le_of_lt
    rw [mul_comm]
    exact Nat.lt_mul_of_div_lt (Nat.lt_add_of_pos_right n.zero_lt_succ) d_pos
  . apply Asymptotics.IsBigO.of_bound 2
    rw [eventually_atTop]
    exists n
    intro b hb
    norm_cast; omega
