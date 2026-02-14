import Mathlib

/-!
**Iran TST 2025 Q9.** Find all sequences $(a_n)$ of natural numbers such that for every pair of natural numbers $r$ and $s$, the following inequality holds:
$$\frac{1}{2} < \frac{\mathrm{gcd}(a_r, a_s)}{\mathrm{gcd}(r, s)} < 2$$
-/


section ForMathlib

attribute [gcongr] Finset.image_subset_image
@[gcongr] theorem Finset.subtype_subset_subtype {α : Type*} {p : α → Prop} [DecidablePred p]
  {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) :
    s₁.subtype p ⊆ s₂.subtype p := by
  grind [Finset.subtype]

namespace PNat
  @[elab_as_elim]
  def recOnPrimeCoprime {motive : ℕ+ → Sort*}
      (prime_pow : ∀ (p : ℕ+) (n : ℕ), Prime p → motive (p ^ n))
      (coprime : (a b : ℕ+) → 1 < a → 1 < b → a.Coprime b → motive a → motive b → motive (a * b))
      (a : ℕ+) : motive a :=
    match a with
    | ⟨x, hx⟩ =>
      x.recOnPrimeCoprime (motive := fun n => ∀ hn, motive ⟨n, hn⟩)
        nofun
        (fun p n hp _ => prime_pow ⟨p, hp.pos⟩ n hp)
        (fun a b ha1 hb1 h ha hb _ =>
          let A : ℕ+ := ⟨a, by omega⟩
          let B : ℕ+ := ⟨b, by omega⟩
          coprime A B ha1 hb1 (coprime_coe (m := A) (n := B) |>.mp h) (ha A.2) (hb B.2))
        hx

  attribute [pnat_to_nat_coe] dvd_iff pow_coe gcd_coe
  @[pnat_to_nat_coe] theorem coprime_coe' {m n : ℕ+} : m.Coprime n ↔ Nat.Coprime ↑m ↑n := by simp

  @[simp] theorem gcd_self (a : ℕ+) : gcd a a = a := by exact_mod_cast Nat.gcd_self a
end PNat

instance Nat.Primes.fact_prime (p : Nat.Primes) : Fact (Nat.Prime p) := ⟨p.2⟩

namespace padicValRat
  variable {p : ℕ} [hp : Fact p.Prime]

  -- why is this protected??
  protected theorem zpow {q : ℚ} (hq : q ≠ 0) (k : ℤ) :
      padicValRat p (q ^ k) = k * padicValRat p q := by
    induction k using Int.negInduction with
    | nat k =>
      rw [zpow_natCast]
      apply padicValRat.pow hq
    | neg ih k =>
      simp_rw [zpow_neg, neg_mul, ← ih, zpow_natCast]
      apply padicValRat.inv

  theorem self_zpow (k : ℤ) : padicValRat p (p ^ k) = k := by
    rw [padicValRat.zpow (by exact_mod_cast hp.1.ne_zero),
      self hp.1.one_lt, mul_one]
end padicValRat

theorem AddCircle.coe_periodic {𝕜 : Type*} [AddCommGroup 𝕜] (p : 𝕜) :
    ((↑) : 𝕜 → AddCircle p).Periodic p :=
  fun _ => coe_add_period ..

open Real in
theorem irrational_logb_prime {p q : ℕ} [hp : Fact (p.Prime)] [hq : Fact (q.Prime)] (hpq : p ≠ q) :
    Irrational (logb p q) := by
  rw [irrational_iff_ne_rational, ← log_div_log]
  intro a b hb h
  symm at h; field_simp [show log p ≠ 0 from log_pos (by exact_mod_cast hp.1.one_lt) |>.ne'] at h
  rw [← log_zpow, ← log_zpow, log_injOn_pos.eq_iff] at h
  replace h : (p ^ a : ℚ) = q ^ b := by rify; exact h
  absurd congr(padicValRat q $h)
  rw [padicValRat.zpow, padicValRat.self_zpow, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (hp.1.dvd_iff_eq hq.1.ne_one |>.not.mpr hpq),
    Nat.cast_zero, mul_zero]
  omega
  all_goals norm_num; positivity [hp.1.pos, hq.1.pos]

end ForMathlib


section IntervalLemma
  open Set Real

  lemma AddCircle.quantitative_density_lemma
    (p : ℝ) [hp : Fact (0 < p)]
    ⦃x : ℝ⦄ (hx : Irrational (x / p))
    (c : ℝ) (hc : c < p) :
      ∃ N : ℕ, ∀ a : ℝ, ∃ i ≤ N,
        i • (x : AddCircle p) ∉ (↑) '' Icc a (a + c) := by
    by_cases hc0 : 0 ≤ c
    case neg => exists 0; simp [hc0]

    have ⟨M, M_pos, k, hkM, hk⟩ : ∃ M : ℕ, 0 < M ∧ ∃ k : ℝ, p / M < k - c ∧ k < p := by
      have ⟨K, hK⟩ := exists_nat_one_div_lt (ε := 1 - c / p) (by bound)
      refine ⟨2 * (K + 1), by simp, p - p / (2 * (K + 1)), ?_, ?_⟩
      . have := hp.1; push_cast; linear_combination (norm := field_simp) (p) * hK; linarith
      . cancel_denoms; bound

    suffices ha (a : ℝ) : ∃ i : ℕ, i • (x : AddCircle p) ∉ (↑) '' Icc a (a + k)
    . suffices
          ∃ S : Finset ℝ, ∀ a : ℝ, ∃ s ∈ S,
            ((↑) '' Icc a (a + c) : Set (AddCircle p)) ⊆ (↑) '' Icc s (s + k) by
        rcases this with ⟨S, hS⟩
        choose f hf using ha
        exists S.sup f + 1
        peel hS with a hS
        rcases hS with ⟨s, hsS, hs⟩
        exists f s
        grind only [!Finset.le_sup, = subset_def]
      exists Finset.range M |>.image (↑· * (p / M))
      intro a
      simp_rw [Finset.mem_image, Finset.mem_range, exists_exists_and_eq_and]
      let a' := Int.fract (a / p)
      let i := ⌊a' * M⌋₊
      refine ⟨i, ?_, ?_⟩
      . rw_mod_cast [Nat.floor_lt', mul_lt_iff_lt_one_left]
        . apply Int.fract_lt_one
        all_goals norm_cast; try omega
      . rw (occs := [1]) [← coe_periodic p |>.zsmul (-⌊a / p⌋) |>.funext]
        erw [image_comp (f := QuotientAddGroup.mk)]
        gcongr
        rw [image_add_const_Icc]
        convert_to Icc (a' * p) (a' * p + c) ⊆ _ using 1
        . have : a' * p + ⌊a / p⌋ • p = a := Int.fract_div_mul_self_add_zsmul_eq _ _ hp.1.ne'
          simp_rw [neg_smul, zsmul_eq_mul] at this ⊢
          congr 1 <;> linarith only [this]
        apply Icc_subset_Icc
        . field_simp [hp.1]
          convert Nat.floor_le _ using 1 <;> (dsimp [a']; try bound)
        . have := hp.1
          have : a' * _ < i + 1 := Nat.lt_floor_add_one _
          field_simp at hkM ⊢
          linear_combination p * this + hkM
    have k_pos : 0 < k := by linarith [show 0 < p / M by bound]
    clear * - hx k_pos hk

    have injOn : InjOn ((↑) : ℝ → AddCircle p) (Ico a (a + p)) :=
      LeftInvOn.injOn (f₁' := (↑) ∘ AddCircle.equivIco p a) <| by
        intro x hx
        lift x to Ico a (a + p) using hx
        simp [AddCircle.equivIco_coe_eq]
    have h_compl : ((↑) '' Icc a (a + k) : Set (AddCircle p))ᶜ = (↑) '' Ioo (a + k) (a + p) := by
      rw [compl_eq_univ_diff, ← AddCircle.coe_image_Ico_eq (p := p) (a := a), ← injOn.image_diff_subset]
        <;> grind
    simp_rw [← mem_compl_iff, h_compl]

    apply DenseRange.exists_mem_open
    . rwa [← denseRange_zsmul_iff_nsmul, AddCircle.denseRange_zsmul_coe_iff]
    . let e := AddCircle.openPartialHomeomorphCoe p (a + k / 2)
      rw [← e.isOpen_symm_image_iff_of_subset_target]
      . change IsOpen (e.symm '' (e '' _))
        convert isOpen_Ioo (a := a + k) (b := a + p)
        erw [e.symm_image_image_of_subset_source]
        rw [AddCircle.openPartialHomeomorphCoe_source]
        apply Ioo_subset_Ioo <;> linarith
      . rw [AddCircle.openPartialHomeomorphCoe_target, ← h_compl, compl_subset_compl, singleton_subset_iff]
        refine ⟨_, ?_, rfl⟩
        rw [mem_Icc]; constructor <;> linarith
    . simp; linarith

  lemma interval_lemma
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    {c : ℝ} (hc : 1 ≤ c ∧ c < q) :
      ∃ N : ℕ, ∀ f : ℕ → ℕ, ∃ i ≤ N, ∃ j ≤ N,
        c * (q ^ f i / p ^ i) < q ^ f j / p ^ j := by
    have ⟨c_nn, hc'⟩ : 0 ≤ log c ∧ log c < log q := by bound
    letI Cq := AddCircle (log q)
    letI Cq.mk : ℝ → Cq := QuotientAddGroup.mk

    have hq' : Fact (0 < log q) := ⟨log_pos (by exact_mod_cast hq.1.one_lt)⟩
    have hN := AddCircle.quantitative_density_lemma (log q) (x := -log p) ?h_irr (log c) hc'
    peel hN with N hN
    intro f

    case h_irr =>
      rw [neg_div, irrational_neg_iff, Real.log_div_log]
      exact irrational_logb_prime hpq.symm

    let g i := log q * f i - log p * i
    have h : ∃ i ≤ N, ∀ j ≤ N, g i ≤ g j := by
      simpa [Nat.lt_add_one_iff] using (Finset.range N.succ).exists_min_image g (by simp)
    /- peel h with i _ h -/ -- TODO why doesn't this work?
    rcases h with ⟨i, hi, h⟩; exists i, hi
    peel hN (g i) with j hj hj'
    replace hj := h j hj
    convert_to (g j : AddCircle (log q)) ∉ _ using 2 at hj'
    . convert_to j • (-log p : AddCircle (log q)) = f j • log q - j • log p
      . simp_rw [g, ← QuotientAddGroup.mk_nat_mul, QuotientAddGroup.mk_sub]; ring_nf
      simp [AddCircle.coe_period (log q)]
    clear * - hc hj hj'

    have : g i + log c < g j := by grind

    suffices hg i : exp (g i) = q ^ f i / p ^ i
    . simp_rw [← hg]
      clear * - hc this
      rw [← log_lt_log_iff, log_mul _ (exp_ne_zero _), log_exp, log_exp] <;> bound
    dsimp [g]
    rw [exp_sub, exp_mul, exp_mul, exp_log, exp_log]
    . norm_cast
    all_goals positivity [hp.1.pos, hq.1.pos]

end IntervalLemma



open PNat

abbrev IsApprox (a b : ℕ+) := a < 2 * b ∧ b < 2 * a

theorem IsApprox.iff_rat (a b : ℕ+) :
    IsApprox a b ↔
    (a / b : ℚ) ∈ Set.Ioo (1 / 2) 2 := by
  rw [IsApprox, Set.mem_Ioo]
  field_simp; norm_cast; tauto

@[ext] structure Data where
  a : ℕ+ → ℕ+
  h' i j : IsApprox (gcd (a i) (a j)) (gcd i j)
attribute [coe] Data.a
instance : FunLike Data ℕ+ ℕ+ := ⟨Data.a, fun a b => by aesop⟩

namespace Data

notation "ℙ" => Nat.Primes

variable (a : Data)

theorem h i j : IsApprox (gcd (a i) (a j)) (gcd i j) := a.h' ..
theorem self i : IsApprox (a i) i := by simpa using a.h i i
theorem coprime i j (h : Coprime i j) : Coprime (a i) (a j) := by
  have := a.h i j
  dsimp only [Coprime, IsApprox] at *
  pnat_to_nat; lia
theorem one : a 1 = 1 := by simpa [Coprime] using a.coprime 1 1 coprime_one
theorem one_lt i (hi : 1 < i) : 1 < a i := by
  have := a.self i
  unfold IsApprox at this
  pnat_to_nat; lia

theorem dvd_six_mul {i j} (hij : i ∣ j) :
    a i ∣ 6 * a j := by
  have h₁ := a.h i j |>.2
  rw [gcd_eq_left_iff_dvd.mpr hij] at h₁
  have h₂ := gcd_dvd_left (a i) (a j)
  have h₃ := a.self i |>.1
  have ⟨c, hc⟩ := exists_eq_mul_right_of_dvd h₂
  have c_hi : c < 4 := by
    pnat_to_nat; nlinarith only [h₁, h₃, hc]
  replace c_hi : c ∣ 6 := by
    pnat_to_nat; interval_cases (c : ℕ) <;> decide
  rw [mul_comm, hc]
  exact mul_dvd_mul (gcd_dvd_right ..) c_hi

-- this is a surprise tool that will help us later
theorem dvd_of_eq {i j} (hij : i ∣ j) (hi : a i = i) :
    i ∣ a j := by
  have := a.h i j |>.2
  pnat_to_nat
  rw [Nat.gcd_eq_left hij, hi] at this
  rw [← Nat.gcd_eq_left_iff_dvd]
  grind only [Nat.eq_of_dvd_of_lt_two_mul, Nat.gcd_dvd_left]

theorem dvd {i j} (hij : i ∣ j) (h2 : ¬ 2 ∣ a i) (h3 : ¬ 3 ∣ a i) :
    a i ∣ a j := by
  have := a.dvd_six_mul hij
  pnat_to_nat
  rwa [Nat.Coprime.dvd_mul_left] at this
  apply Nat.Coprime.symm
  apply Nat.Coprime.mul_left (m := 2) (n := 3) <;> rw [Nat.Prime.coprime_iff_not_dvd]
  exacts [h2, prime_two, h3, prime_three]


def PrimesOver (p : ℙ) := { q : ℙ | ∃ k, ↑q ∣ a (↑p ^ k) }
local notation3 "Q" => a.PrimesOver

open Function in
theorem disj : Pairwise (Disjoint on Q) := fun i j h => by
  rw [onFun, Set.disjoint_iff]
  intro q ⟨⟨ki, hi⟩, ⟨kj, hj⟩⟩
  have := coprime_coe.mpr <| a.coprime (i ^ ki) (j ^ kj) <| coprime_coe.mp <|
    Nat.coprime_pow_primes ki kj i.2 j.2 <| by rwa [ne_eq, Subtype.coe_inj, Nat.Primes.coe_pnat_inj]
  rw [dvd_iff] at hi hj
  exact Nat.not_coprime_of_dvd_of_dvd (d := q) q.2.one_lt hi hj this

theorem nonempty {p} : (Q p).Nonempty :=
  have ⟨q, hq, h⟩ := exists_prime_and_dvd (a.one_lt p p.2.one_lt).ne'
  ⟨⟨q, hq⟩, 1, by simpa using h⟩

open scoped Classical in
noncomputable def LeastPrimeOver (p : ℙ) : ℙ :=
  ⟨PNat.find (p := (∃ q : ℙ, q = · ∧ q ∈ Q p)) (by simpa using a.nonempty),
   by generalize_proofs h; rcases PNat.find_spec h with ⟨q, h, hq⟩; exact h ▸ q.2⟩
local notation3 "q₀" => a.LeastPrimeOver

theorem q₀_mem p : q₀ p ∈ Q p := by
  classical unfold LeastPrimeOver; generalize_proofs h; rcases PNat.find_spec h with ⟨q, h, hq⟩; simpa [← h]

theorem q₀_le_of_mem {p q} (h : q ∈ Q p) : (q₀ p : ℕ+) ≤ q := by
  classical unfold LeastPrimeOver; generalize_proofs h; apply PNat.find_le (n := q) (h := h); exists q

theorem q₀_injective : Function.Injective q₀ := fun i j h => by
  contrapose! h
  exact a.disj h |>.ne_of_mem (a.q₀_mem i) (a.q₀_mem j)

theorem q₀_le_of_four_le {p : ℙ} (hp : 4 ≤ (p : ℕ+)) : (q₀ p : ℕ+) ≤ p := by
  by_cases! hq₀ : (q₀ p : ℕ+) < 4
  . pnat_to_nat; lia
  have ⟨h2, h3⟩ : ⟨2, Nat.prime_two⟩ ∉ Q p ∧ ⟨3, Nat.prime_three⟩ ∉ Q p := by
    constructor; all_goals
    apply mt <| hq₀.trans ∘ a.q₀_le_of_mem
    norm_cast
  by_contra! hQ
  suffices (k : ℕ) : (p + 1) ^ k ≤ a (p ^ k)
  . apply isLittleO_pow_pow_of_lt_left (r₁ := p) (r₂ := p + 1) (by simp) (by simp)
      |>.not_isBigO <| .of_forall <| by simp [p.2.ne_zero]
    refine .of_bound 2 <| .of_forall fun k => ?_
    exact_mod_cast (this k |>.trans_lt <| a.self _ |>.1).le
  induction k with | zero => simp | succ k ih
  have := a.self (p ^ k) |>.1
  have ⟨c, hc⟩ := exists_eq_mul_right_of_dvd <|
    a.dvd (i := p ^ k) (j := p ^ (k + 1)) (pow_dvd_pow _ <| by simp)
      (h2 ⟨k, ·⟩) (h3 ⟨k, ·⟩)
  obtain rfl | c_lo : c = 1 ∨ p < c :=
    eq_bot_or_bot_lt c |>.imp_right fun h => by
      have ⟨q, hq, h⟩ := exists_prime_and_dvd h.ne'
      grw [← le_of_dvd h]
      apply hQ.trans_le
      apply a.q₀_le_of_mem (q := ⟨q, hq⟩)
      exists k + 1
      show q ∣ _; grw [h, hc, ← dvd_mul_left]
  . have this' := a.self (p ^ (k + 1)) |>.2
    rw [pow_succ] at this' hc
    pnat_to_nat; exfalso; nlinarith only [this, hc, this', hp]
  rw [hc, pow_succ]
  pnat_to_nat; nlinarith only [c_lo, ih]

open Finset in
theorem q₀_surjective : Function.Surjective q₀ := by
  intro p
  have ⟨N, hp, hq⟩ : ∃ N : ℕ+, p ≤ N ∧ ∀ q : ℙ, q ≤ N → q₀ q ≤ N := by
    let M : ℕ+ := Iio 4 |>.subtype Nat.Prime |>.sup (q₀ ·)
    have hM (p : ℙ) (hp : (p : ℕ+) < 4) : q₀ p ≤ M := by
      apply le_sup (b := p)
      rwa [mem_subtype, mem_Iio]
    existsi max p M
    grind only [= max_def, ! q₀_le_of_four_le]
  let S : Finset ℙ := .subtype Nat.Prime <| Iic N
  have hS {q} : q ∈ S ↔ q ≤ N := by rw [mem_subtype, mem_Iic]; norm_cast
  replace hp : p ∈ S := hS.mpr hp
  replace hq : map ⟨q₀, a.q₀_injective⟩ S ⊆ S := by
    simp_rw [map_eq_image, image_subset_iff, hS]; exact hq
  apply map_eq_of_subset at hq
  rw [← hq] at hp
  simp at hp; tauto

open Set in
/--
The set of primes over p is a singleton for each p.
-/
theorem eq_singleton {p} : Q p = {q₀ p} := by
  rw [eq_singleton_iff_unique_mem]
  refine ⟨a.q₀_mem p, ?_⟩
  intro u hu
  obtain ⟨q, rfl⟩ := a.q₀_surjective u
  rw [a.disj.eq <| not_disjoint_iff.mpr ⟨q₀ q, hu, a.q₀_mem q⟩]


def MovingPrimes.ht (p q : ℙ) (x : ℕ × ℕ) : ℕ+ := p ^ x.1 * q ^ x.2
open MovingPrimes in
structure MovingPrimes where
  (p q p' q' : ℙ)
  (hp : (p : ℕ) ≠ p') (hq : (q : ℕ) ≠ q')
  (hpq' : (4 : ℕ) < p' * q')
  f : ℕ × ℕ → ℕ × ℕ
  f₁ i := f (i, 0) |>.1
  f₂ j := f (0, j) |>.2
  hf₁ i : f (i, 0) = (f₁ i, 0)
  hf₂ j : f (0, j) = (0, f₂ j)
  h x y : IsApprox (ht p' q' (f x ⊓ f y)) (ht p q (x ⊓ y))
  -- this follows from h but might as well provide it for funsies
  lo₁ x : f₁ x.1 - 1 ≤ (f x).1
  lo₂ x : f₂ x.2 - 1 ≤ (f x).2

namespace MovingPrimes

variable (self : MovingPrimes)

def symm : MovingPrimes :=
  let { p, q, p', q', hp, hq, hpq', f, f₁, f₂, hf₁, hf₂, h, lo₁, lo₂ } := self
  { p := q, q := p, p' := q', q' := p'
    hp := hq, hq := hp, hpq' := by grind
    f := Prod.swap ∘ f ∘ Prod.swap
    f₁ := f₂, f₂ := f₁
    hf₁ := by grind, hf₂ := by grind
    h x y := by
      specialize h x.swap y.swap
      grind only [Prod.inf_def, ht, = Prod.swap_prod_mk]
    lo₁ := lo₂ ∘' Prod.swap
    lo₂ := lo₁ ∘' Prod.swap }

-- some of these only come in useful later
lemma ht_add p q x y : ht p q (x + y) = ht p q x * ht p q y := by dsimp [ht]; ring
lemma ht_dvd p q ⦃x y⦄ (h : x ≤ y) : ht p q x ∣ ht p q y := by
  obtain ⟨k, rfl⟩ := exists_add_of_le h; simp [ht_add]
lemma ht_mono p q : Monotone (ht p q) := by
  intro x y h
  obtain ⟨k, rfl⟩ := exists_add_of_le h; simp [ht_add]

open Finsupp in
section
  lemma factorization_ht p q x :
      Nat.factorization (ht p q x) = (fun₀ | p => x.1) + (fun₀ | q => x.2) := by
    simp only [ht, mul_coe, pow_coe, ne_eq, Nat.pow_eq_zero, ne_zero, false_and, not_false_eq_true,
      Nat.factorization_mul]
    simp only [Nat.Primes.coe_pnat_nat, p.2, q.2, Nat.Prime.factorization_pow]

  lemma factorization_ht' {p q} (hpq : p ≠ q) x :
      Nat.factorization (ht p q x) = fun₀ | p => x.1 | q => x.2 := by
    rw [factorization_ht, update_eq_single_add, add_comm]
    simp [Nat.Primes.coe_nat_inj, hpq]

  lemma primeFactors_ht p q x : Nat.primeFactors (ht p q x) ⊆ {↑p, ↑q} := by
    rw [← Nat.support_factorization, factorization_ht]
    grind [support_single_subset, support_add]

  lemma subtype_primeFactors_ht p q x :
      (Nat.primeFactors (ht p q x)).subtype Nat.Prime ⊆ {p, q} := by
    grw [primeFactors_ht]
    intro; aesop

  lemma ht_inf {p q} (hpq : p ≠ q) x y : ht p q (x ⊓ y) = gcd (ht p q x) (ht p q y) := by
    pnat_to_nat
    rw [← Nat.factorization_inj.eq_iff (by simp) (by simp)]
    rw [Nat.factorization_gcd (ne_zero _) (ne_zero _)]
    repeat rw [factorization_ht' hpq]
    ext; simp [Finsupp.single_apply, Function.update_apply]; grind
end

def hi.C (p q : ℙ) : ℕ := max (Nat.clog p (8 * q)) (Nat.clog q (8 * p))

lemma hi.ht_lemma₁ p q x y : 8 * ht p q (x, y) ≤ ht p q (x + C p q, y - 1) := by
  dsimp [ht]
  calc
    _ ≤ 8 * (p ^ x * (q ^ (1 + (y - 1))) : ℕ+) := by
      gcongr
      . apply PNat.one_le
      . omega
    _ = ((8 * q) * p ^ x) * q ^ (y - 1) := by ring
    _ ≤ p ^ (x + Nat.clog p (8 * q)) * q ^ (y - 1) := by
      rw [add_comm, pow_add]
      gcongr
      apply Nat.le_pow_clog p.2.one_lt
    _ ≤ _ := by gcongr; exacts [p.2.one_le, le_max_left ..]

lemma hi.ht_lemma₂ p q x y : 8 * ht p q (x, y) ≤ ht p q (x - 1, y + C p q) := by
  convert ht_lemma₁ q p y x using 1 <;> dsimp [ht, C]
  . ring
  . rw [max_comm]; ring

local notation3 "p" => self.p
local notation3 "q" => self.q
local notation3 "p'" => self.p'
local notation3 "q'" => self.q'
local notation3 "f" => self.f
local notation3 "f₁" => self.f₁
local notation3 "f₂" => self.f₂

theorem h_self x : IsApprox (ht p' q' (f x)) (ht p q x) := by
  convert self.h x x using 2 <;> simp
lemma h_self₁ i : IsApprox (p' ^ f₁ i) (p ^ i) := by
  convert self.hf₁ i ▸ self.h_self (i, 0) <;> simp [ht]
lemma h_self₂ j : IsApprox (q' ^ f₂ j) (q ^ j) :=
  self.symm.h_self₁ j

open hi in
theorem hi x : (f x).1 ≤ f₁ x.1 + C p' q' ∧ (f x).2 ≤ f₂ x.2 + C p' q' := by
  have hlo : ht p q x < 4 * ht p' q' (f₁ x.1, f₂ x.2) := by
    convert mul_lt_mul_of_lt_of_lt (self.h_self₁ x.1).2 (self.h_self₂ x.2).2 using 1
    dsimp [ht]; ring
  have hf := self.h_self x |>.1
  constructor <;> by_contra! h
  . have := ht_lemma₁ p' q' (f₁ x.1) (f₂ x.2) |>.trans <| ht_mono p' q' (b := f x) ⟨h.le, self.lo₂ x⟩
    pnat_to_nat; lia
  . have := ht_lemma₂ p' q' (f₁ x.1) (f₂ x.2) |>.trans <| ht_mono p' q' (b := f x) ⟨self.lo₁ x, h.le⟩
    pnat_to_nat; lia

theorem inc.step₁ i j (hj : j ≤ 1) : f₁ i + j ≤ f₁ (i + j + 1) := by
  by_contra! h
  replace h : (p' : ℕ+) ^ (f₁ (i + j + 1) + 1) ≤ p' ^ (f₁ i + j) := by
    gcongr 1
    . apply PNat.one_le -- TODO: sad that positivity doesn't know this
    . omega
  have : 4 * (p' : ℕ+) ^ j ≤ p ^ (j + 1) * p' := by
    pnat_to_nat; interval_cases j <;> simp [pow_two] <;> nlinarith only [p.2.two_le, p'.2.two_le]
  have h₁ := self.h_self₁ i |>.1
  have h₂ := self.h_self₁ (i + j + 1) |>.2
  -- TODO: would be nice if linear_combination could handle contradictory inequality chains like this,
  -- instead of having to pick one to use
  absurd h₁; push_neg; rw [← mul_le_mul_iff_left (p' ^ j * p ^ (j + 1) : ℕ+)]
  pnat_to_nat; push_cast at *
  linear_combination p ^ (j + 1) * h + 2 * p' ^ j * h₂ + p' ^ f₁ (i + j + 1) * this

theorem inc.step i j (hj : j ≤ 1) : f₁ i + j ≤ f₁ (i + j + 1) ∧ f₂ i + j ≤ f₂ (i + j + 1) :=
  ⟨inc.step₁ self i j hj, inc.step₁ self.symm i j hj⟩

theorem inc i j (hij : i < j) : f₁ i + (j - i) / 2 ≤ f₁ j ∧ f₂ i + (j - i) / 2 ≤ f₂ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.nat_succ_le
  clear hij
  rw [Nat.succ_eq_add_one, show i + 1 + k - i = k + 1 by omega]
  induction k using Nat.twoStepInduction with
  | zero => simpa using inc.step self i 0 (by simp)
  | one => simpa using inc.step self i 1 (by simp)
  | more k ih₁ ih₂ => have := inc.step self (i + 1 + k) 1 (by simp); lia

def buffer := 2 * (hi.C p' q' + 1)

section
  local grind_pattern hi => self.f x
  local grind_pattern lo₁ => self.f x
  local grind_pattern lo₂ => self.f x

  @[grind .] theorem le₁ x y (h : x.1 + self.buffer ≤ y.1) : (f x).1 ≤ (f y).1 := by
    have := self.inc x.1 y.1 (by grind [buffer]) |>.1; grind [buffer]
  @[grind .] theorem le₂ x y (h : x.2 + self.buffer ≤ y.2) : (f x).2 ≤ (f y).2 := by
    have := self.inc x.2 y.2 (by grind [buffer]) |>.2; grind [buffer]
end

include self in
theorem boom : False := by
  open Filter Set in
  have ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℝ, (1 ≤ a ∧ a < p') ∧ (1 ≤ b ∧ b < q') ∧ 4 ≤ a * b := by
    have ⟨⟨a, b⟩, h, ha, hb⟩ := tendsto_mul (M := ℝ) (a := p') (b := q')
      |>.eventually_const_le (u := 4) (by exact_mod_cast self.hpq')
      |>.and_frequently («q» := (fun x => x.1 ∈ Ico 1 ↑p' ∧ x.2 ∈ Ico 1 ↑q')) ?_
      |>.exists
    exact ⟨a, b, ha, hb, h⟩
    rw [nhds_prod_eq, frequently_prod_and, frequently_mem_iff_neBot, frequently_mem_iff_neBot,
      ← nhdsWithin, ← nhdsWithin]
    apply_rules [And.intro, right_nhdsWithin_Ico_neBot] <;> norm_cast
    exacts [p'.2.one_lt, q'.2.one_lt]

  have ⟨N₁, hN₁⟩ := interval_lemma self.hp ha
  have ⟨N₂, hN₂⟩ := interval_lemma self.hq hb

  let g₁ i := f (i, N₂ + self.buffer) |>.1
  let g₂ j := f (N₁ + self.buffer, j) |>.2
  rcases hN₁ g₁ with ⟨i₁, hi₁, i₂, hi₂, hi⟩; clear hN₁
  rcases hN₂ g₂ with ⟨j₁, hj₁, j₂, hj₂, hj⟩; clear hN₂

  have hg {i} (hi : i ≤ N₁) {j} (hj : j ≤ N₂) : IsApprox (ht p' q' (g₁ i, g₂ j)) (ht p q (i, j)) := by
    convert self.h (i, N₂ + self.buffer) (N₁ + self.buffer, j) using 2
      <;> grind only [Prod.inf_def, inf_eq_left, inf_eq_right, le₁, le₂]
  simp_rw [ht, IsApprox.iff_rat, Set.mem_Ioo] at hg
  have hg₁ := hg hi₁ hj₁ |>.1
  have hg₂ := hg hi₂ hj₂ |>.2
  clear hg; rify at hg₁ hg₂
  field_simp at *
  have h₁ := mul_lt_mul_of_pos hi hj
    (by positivity [ha.1, p.2.pos, p'.2.pos]) (by positivity [q.2.pos, q'.2.pos])
  have h₂ := mul_lt_mul_of_pos hg₁ hg₂ (by norm_num) (by norm_num)
  ring_nf at h₁ h₂
  have := h₁.trans h₂
  field_simp [p.2.pos, q.2.pos, p'.2.pos, q'.2.pos] at this
  linarith

end MovingPrimes


theorem q₀_dvd_self (p : ℙ) : (q₀ p : ℕ+) ∣ a p := by
  have ⟨q, hq, h⟩ := exists_prime_and_dvd (a.one_lt p p.2.one_lt).ne'
  have h' : ⟨q, hq⟩ ∈ Q p := ⟨1, by rwa [pow_one]⟩
  rw [eq_singleton, Set.mem_singleton_iff] at h'
  rwa [← h']

theorem factors_subset (n : ℕ+) (p : ℙ) (hp : ↑p ∣ a n) :
    ∃ q : ℙ, ↑q ∣ n ∧ q₀ q = p := by
  have ⟨q, hq⟩ := a.q₀_surjective p
  refine ⟨q, ?_, hq⟩
  by_contra! h
  replace h := a.coprime q n <| by
    pnat_to_nat; erw [q.2.coprime_iff_not_dvd]; exact h
  have h' := hq ▸ a.q₀_dvd_self q
  absurd p.2.ne_one
  pnat_to_nat; exact Nat.eq_one_of_dvd_coprimes h h' hp

-- this whole "subtype primeFactors" dance is a little annoying
-- but it's irreducible badness with the way I've done this
-- (unless I define PNat.primeFactors which brings its own set of pains)
open Finset in
theorem subtype_primeFactors_subset (n : ℕ+) :
    (Nat.primeFactors (a n) |>.subtype Nat.Prime) ⊆
    image q₀ (Nat.primeFactors n |>.subtype _) := by
  intro (p : ℙ) hp
  rw [mem_subtype, Nat.mem_primeFactors] at hp
  rcases hp with ⟨-, hp, -⟩
  have ⟨q, hq, h⟩ := a.factors_subset n p (dvd_iff.mpr hp)
  rw [mem_image]
  existsi q
  rw [mem_subtype, Nat.mem_primeFactors]
  exists ⟨q.2, dvd_iff.mp hq, n.ne_zero⟩

theorem eq_pow_q₀ (p : ℙ) i : ∃ k : ℕ, a (p ^ i) = q₀ p ^ k := by
  have := Nat.eq_prime_pow_of_unique_prime_dvd (a (p ^ i)).ne_zero (p := q₀ p) ?_
  . pnat_to_nat; simp [Nat.Primes.coe_pnat_nat]; tauto
  intro q hq h
  have ⟨r, hr, h'⟩ := a.factors_subset _ ⟨q, hq⟩ (dvd_iff.mpr h)
  obtain rfl : r = p := r.coe_nat_inj p |>.mp <|
    Nat.prime_eq_prime_of_dvd_pow r.2 p.2 (dvd_iff.mp hr)
  rw [h']

open Nat renaming factorization → F in
open Nat Finset MovingPrimes in
theorem q₀_eq p : q₀ p = p := by
  revert p
  by_contra! h
  rcases h with ⟨p, hp⟩
  let q := q₀ p
  have hq : q₀ q ≠ q := a.q₀_injective.ne hp

  set p' := q₀ p
  set q' := q₀ q
  have hpq' : p' ≠ q' := hq.symm

  let unht (u v : ℙ) (n : ℕ+) := (F n u, F n v)
  let f := unht p' q' ∘ a ∘ ht p q

  open Finsupp in
  have ht_unht {u v : ℙ} (huv : u ≠ v) (x : ℕ+)
      (hx : (Finset.subtype Nat.Prime <| primeFactors x) ⊆ {u, v}) :
      ht u v (unht u v x) = x := by
    rw [← PNat.coe_inj, ← factorization_inj.eq_iff (ne_zero _) (ne_zero _),
      factorization_ht' huv]
    show (fun₀ | (u : ℕ) => F x u | v => F x v) = F x
    rw [← support_factorization] at hx
    replace hx : (F x).support ⊆ {↑u, ↑v} := by
      convert ← map_subset_map (f := .subtype _) |>.mpr hx <;> aesop
    have this a := F x |>.notMem_support_iff (a := a)
    ext; simp [single_apply, Function.update_apply]; grind

  have ht_f x : ht p' q' (f x) = a (ht p q x) := by
    dsimp [f]
    apply ht_unht hpq'
    grw [subtype_primeFactors_subset, subtype_primeFactors_ht]
    simp [p', q']

  have h_lo {u v} (huv : u ∣ v) {r : ℙ} : F (a u) r - 1 ≤ F (a v) r := by
    rw [tsub_le_iff_left]
    have := a.dvd_six_mul huv
    rw [dvd_iff, ← factorization_le_iff_dvd (ne_zero _) (ne_zero _)] at this
    grw [this r]
    rw [PNat.mul_coe, Nat.factorization_mul (ne_zero _) (ne_zero _),
      add_apply, val_ofNat, add_le_add_iff_right]
    suffices Squarefree 6 from this.natFactorization_le_one _
    rw [squarefree_iff_nodup_primeFactorsList] <;> simp

  apply boom
    { p, q, p', q', f
      hp := p.coe_nat_inj _ |>.not.mpr hp.symm
      hq := q.coe_nat_inj _ |>.not.mpr hq.symm
      hpq' := by
        contrapose! hpq'
        rw [← Nat.Primes.coe_nat_inj]
        nlinarith only [hpq', p'.2.two_le, q'.2.two_le]
      hf₁ i := by
        suffices (f (i, 0)).2 = 0 by grind
        dsimp [f, unht]
        grw [← notMem_support_iff, support_factorization, ← mem_subtype,
          subtype_primeFactors_subset, ← support_factorization, factorization_ht,
          single_zero, add_zero, support_single_subset]
        rw [show Finset.subtype Nat.Prime {↑p} = {p} by clear * - p; aesop]
        grind
      hf₂ j := by
        suffices (f (0, j)).1 = 0 by grind
        dsimp [f, unht]
        grw [← notMem_support_iff, support_factorization, ← mem_subtype,
          subtype_primeFactors_subset, ← support_factorization, factorization_ht,
          single_zero, zero_add, support_single_subset]
        rw [show Finset.subtype Nat.Prime {↑q} = {q} by clear_value q; clear * - q; aesop]
        grind
      h x y := by
        rw [ht_inf, ht_inf, ht_f, ht_f]
        exacts [a.h _ _, hp.symm, hpq']
      lo₁ x := h_lo <| ht_dvd p q <| by simp [Prod.le_def]
      lo₂ x := h_lo <| ht_dvd p q <| by simp [Prod.le_def] }


theorem eq x : a x = x := by
  induction x using recOnPrimeCoprime with
  | prime_pow p n hp =>
    have := a.eq_pow_q₀ ⟨p, hp⟩ n
    rw [a.q₀_eq] at this
    change ∃ k, a (p ^ n) = p ^ k at this
    rcases this with ⟨k, hk⟩
    have ha := a.self (p ^ n)
    rw [hk] at ha ⊢; clear hk
    suffices {m n : ℕ} (h : p ^ m < 2 * p ^ n) : m ≤ n
    . rw [le_antisymm (this ha.1) (this ha.2)]
    contrapose! h
    pnat_to_nat
    grw [← pow_le_pow_right' hp.one_le h.nat_succ_le, pow_succ', hp.two_le]
  | coprime x y hx1 hy1 h hx hy =>
    have hxd := a.dvd_of_eq (dvd_mul_right x y) hx
    have hyd := a.dvd_of_eq (dvd_mul_left y x) hy
    pnat_to_nat
    exact Nat.eq_of_dvd_of_lt_two_mul (ne_zero _) (h.mul_dvd_of_dvd_of_dvd hxd hyd) (a.self (x * y) |>.1)

end Data


theorem problem
  (a : ℕ+ → ℕ+) :
    (∀ r s, ((a r).gcd (a s) / r.gcd s : ℚ) ∈ Set.Ioo (1 / 2) 2) ↔
    a = id := by
  refine ⟨fun h => funext fun x => ?_, fun h => by norm_num [h]⟩
  simp_rw [← IsApprox.iff_rat] at h
  let d : Data := { a, h' := h }
  apply d.eq

/--
info: 'problem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms problem
