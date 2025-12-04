import Mathlib

/-
  A regular simple polygon with ≥ 3 vertices whose vertices are integer lattice points is a square.
-/

open EuclideanGeometry Function AffineMap Polynomial IntermediateField Real Complex Set

attribute [local instance] Complex.finrank_real_complex_fact
noncomputable local instance : Module.Oriented ℝ ℂ (Fin 2) := ⟨Complex.orientation⟩

example
  (n : ℕ) [NeZero n] (hn : 3 ≤ n)
  (P : ZMod n → ℂ) (hP : ∀ i, P i ∈ Algebra.adjoin ℤ {I})
  (A : Real.Angle) (hA : ∀ i, ∡ (P i) (P (i + 1)) (P (i + 2)) = A)
  (L : ℝ) (hL : ∀ i, dist (P i) (P (i + 1)) = L)
  (h_simple : Pairwise (Disjoint on (fun i => lineMap (P i) (P (i + 1)) '' Ico (α := ℝ) 0 1))) :
    n = 4 := by
  -- The vertices are distinct
  have P_inj : Injective P := fun i j h => by
    have hmem k : P k ∈ lineMap (P k) (P (k + 1)) '' Ico (α := ℝ) 0 1 := ⟨0, by simp⟩
    contrapose! h
    exact h_simple h |>.ne_of_mem (hmem i) (hmem j)

  -- Rewrite in terms of vectors corresponding to sides
  let D i := P (i + 1) - P i
  have hD {i} : D i = P (i + 1) - P i := rfl
  have hD' {i} : D (i + 1) = P (i + 2) - P (i + 1) := by simp [D, add_assoc]; norm_cast
  have D_nz {i} : D i ≠ 0 := by
    rw [sub_ne_zero, P_inj.ne_iff]
    simp [ZMod.one_eq_zero_iff]; omega
  replace hL i : ‖D i‖ = L := dist_eq_norm_sub' _ _ |>.symm.trans <| hL i
  replace hA i : (D (i + 1) / D i).arg = A + π := by
    erw [← hA i, oangle, Complex.oangle]
    rw [vsub_eq_sub, vsub_eq_sub, ← hD', ← neg_sub, ← hD,
      arg_mul_coe_angle, arg_div_coe_angle, arg_conj_coe_angle, arg_neg_coe_angle]
    . abel
    all_goals simp [D_nz]

  -- Show that z := D_{i+1} / D_i is a constant, and deduce a geometric series formula for P_i - P_0
  have (eq := hz) z := D 1 / D 0
  replace hz i : D (i + 1) / D i = z := by
    rw [show z = D (0 + 1) / D 0 by convert hz; norm_num]
    apply ext_norm_arg
    . simp [hL]
    . simp_rw [← arg_coe_angle_eq_iff, hA]
  have hDz (i : ℕ) : D i = z ^ i * D 0 := by
    induction i with | zero => simp | succ i h
    push_cast
    rw [pow_succ', mul_assoc, ← h, ← hz i]
    field_simp [D_nz]
  have hPz (i : ℕ) : (P i - P 0) = (∑ j ∈ .range i, z ^ j) * D 0 := by
    induction i with | zero => simp | succ i h
    push_cast
    rw [Finset.sum_range_succ, add_mul, ← h, ← hDz, hD]
    ring

  have z_n1 : z ≠ 1 := by
    rintro rfl
    specialize hPz n
    simp [D_nz] at hPz; omega

  -- z is a primitive n-th root of unity
  have z_prim : IsPrimitiveRoot z n :=
    { pow_eq_one := by
        specialize hDz n
        rw [CharP.cast_eq_zero] at hDz
        linear_combination (norm := skip) -hDz / D 0
        field_simp [D_nz]; ring
      dvd_of_pow_eq_one l hl := by
        specialize hPz l
        rw [geom_sum_eq z_n1, hl] at hPz
        replace hPz : P l = P 0 := by simpa [sub_eq_zero] using hPz
        rwa [P_inj.eq_iff, ZMod.natCast_eq_zero_iff] at hPz }
  clear * - hn hP hD D_nz hz z_prim

  -- lift z to ℚ(i), and discard the other stuff
  lift P to ZMod n → ℚ⟮I⟯
  . peel hP with i hP
    generalize P i = x at hP ⊢
    induction hP using Algebra.adjoin_induction with
    | mem x hx =>
      rw [mem_singleton_iff] at hx; rcases hx with rfl
      apply IntermediateField.mem_adjoin_simple_self
    | algebraMap | add | mul => aesop
  clear_value D
  lift D to ZMod n → ℚ⟮I⟯
  . aesop
  clear P hP hD
  lift z to ℚ⟮I⟯
  . rw [← hz 0]; aesop
  clear * - hn z_prim

  -- show that i has min poly x^2 + 1
  let pI : ℚ[X] := .X ^ 2 + 1
  have pI_deg : pI.natDegree = 2 := natDegree_X_pow_add_C
  have hpI : minpoly ℚ I = pI := by
    have monic : pI.Monic := by apply monic_X_pow_add_C; norm_num
    symm; apply minpoly.eq_of_irreducible_of_monic _ _ monic
    . rw [monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
      . rw [roots_eq_zero_iff_isRoot_eq_bot (pI.ne_zero_of_natDegree_gt (n := 1) (by omega))]
        ext x
        suffices ¬ x ^ 2 + 1 = 0 by simpa [pI]
        nlinarith
      all_goals omega
    . simp [pI]

  -- manually handle n = 3 and n = 6, by showing that e^(2πi/3) isn't in ℚ(i)
  have : cexp ((2 * π / 3 : ℝ) * I) ∉ ℚ⟮I⟯ := by
    set c := cexp (↑(2 * π / 3) * I) with hc
    clear_value c
    intro h
    lift c to ℚ⟮I⟯ using h

    let pb := adjoin.powerBasis isIntegral_rat_I
    have pb_dim : pb.dim = 2 := by rw [adjoin.powerBasis_dim, hpI, pI_deg]
    obtain ⟨f, f_deg, rfl⟩ := pb.exists_eq_aeval c
    rw [pb_dim] at f_deg
    obtain ⟨x, y, rfl⟩ := f.exists_eq_X_add_C_of_natDegree_le_one (by omega)

    simp only [map_add, map_mul, aeval_C, eq_ratCast, aeval_X,
      AddMemClass.coe_add, MulMemClass.coe_mul, SubfieldClass.coe_ratCast] at hc
    erw [AdjoinSimple.coe_gen] at hc
    replace hc := congr(im $hc)
    simp only [add_im, mul_im, ratCast_re, I_im, mul_one, ratCast_im, I_re, mul_zero, add_zero] at hc
    rw [exp_ofReal_mul_I_im, show 2 * π / 3 = π - π / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three] at hc
    cancel_denoms at hc; norm_cast at hc
    absurd Nat.prime_three.irrational_sqrt
    exists 2 * x

  replace this (c : ℚ⟮I⟯) : ¬ IsPrimitiveRoot c 3 := by
    rw [← IsPrimitiveRoot.map_iff_of_injective (FaithfulSMul.algebraMap_injective _ ℂ)]
    rw [IntermediateField.algebraMap_apply, isPrimitiveRoot_iff (hn := by norm_num)]
    push_neg; intro i hi hi' h
    interval_cases i
    . norm_num at hi'
    . absurd h ▸ c.2
      convert this using 3; push_cast; ring
    . absurd h ▸ c.2
      rw [← inv_mem_iff, ← Complex.exp_neg, ← Complex.exp_periodic]
      convert this using 3; push_cast; ring

  have z_prim' : IsPrimitiveRoot z n := by
    rwa [← IntermediateField.algebraMap_apply,
      IsPrimitiveRoot.map_iff_of_injective (FaithfulSMul.algebraMap_injective _ ℂ)] at z_prim
  obtain rfl | rfl | hn : n = 3 ∨ n = 6 ∨ (4 ≤ n ∧ n ≠ 6) := by omega
  . absurd z_prim'; apply this
  . absurd z_prim'.pow_of_dvd (p := 2) (by norm_num) (by norm_num); apply this

  -- show that ϕ n ≤ [ℚ : ℚ(i)] = 2
  have _ : FiniteDimensional ℚ ℚ⟮I⟯ := by
    apply finiteDimensional_adjoin
    simp [isIntegral_rat_I]
  have hz := minpoly.natDegree_le (K := ℚ) z
  grw [minpoly_eq,
    minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) _ (z_prim.isIntegral (by omega)),
    natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
    ← z_prim.totient_le_degree_minpoly, adjoin.finrank isIntegral_rat_I,
    hpI, pI_deg] at hz
  clear * - hn hz

  -- it suffices that 3 ≤ ϕ n when n ≥ 5, ≠ 6
  suffices h n (hn : 5 ≤ n ∧ n ≠ 6) : 3 ≤ n.totient
  . by_contra!
    specialize h n (by omega)
    omega
  obtain rfl | hn : n = 5 ∨ 7 ≤ n := by omega
  . decide
  clear * - hn

  induction n using Nat.prime_composite_induction with
  | zero | one => contradiction
  | prime p hp => rw [Nat.totient_prime hp]; omega
  | composite a ha iha b hb ihb
  wlog hab : a ≤ b
  . grind
  obtain hb' | hb' := lt_or_ge b 7
  case inr =>
    grw [← Nat.totient_super_multiplicative, ihb hb',
      ← show 1 ≤ a.totient by rw [Nat.succ_le_iff, Nat.totient_pos]; omega, one_mul]
  revert hn
  interval_cases b <;> interval_cases a <;> decide
