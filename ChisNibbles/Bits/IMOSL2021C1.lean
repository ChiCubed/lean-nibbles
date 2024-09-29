import Mathlib

/-
A formalisation of the main solution ingredient for IMO Shortlist 2021 C1
-/

open Set

example
  {S : Type*} [Infinite S]
  (f: S → S → ℕ)
  (hs : ∀ a b, f a b = f b a)
  (ht : ∀ a b c, a ≠ c → f a b = f b c → f a b = f a c)
  (hf : ∀ a, Finite $ Set.range (f a)) :
    ∃ i, ∀ a b, a ≠ b → f a b = i := by
  have pig a (s : Set S) (hs : s.Infinite) :
      ∃ t ⊆ s, t.Infinite ∧ ∃ i, ∀ {x}, x ∈ t → f a x = i := by
    haveI := hs.to_subtype
    have ⟨y, hy⟩ := Finite.exists_infinite_fiber $ restrict s $ rangeFactorization (f a)
    refine ⟨s ∩ f a ⁻¹' {y.1}, inter_subset_left, ?_, y, by simp⟩
    rw [← infinite_coe_iff]
    apply @Infinite.of_injective _ _ hy fun ⟨⟨x, h⟩, hx⟩ => ⟨x, by aesop⟩
    intro; aesop
  have tri {a b c i} (h : b ≠ c) : f a b = i → f a c = i → f b c = i :=
    fun k l =>
      have m := hs .. |>.trans k
      .symm $ m.symm.trans $ ht b a c h $ m.trans l.symm

  have ⟨x⟩ := Infinite.nonempty S
  have ⟨s, x_s, sin, i, hi⟩ := pig x {x}ᶜ (finite_singleton x).infinite_compl
  rw [subset_compl_singleton_iff] at x_s

  suffices ∃ i, ∀ b, x ≠ b → f x b = i by
    rcases this with ⟨i, hi⟩
    exists i
    intro a
    by_cases ha : x = a
    . exact ha.symm ▸ hi
    intro b h
    by_cases hb : x = b
    . subst hb; exact hs .. ▸ hi a h.symm
    exact tri h (hi _ ha) (hi _ hb)
  by_contra! hb
  specialize hb i
  rcases hb with ⟨b, x_b, hb⟩
  have ⟨t, t_s, tin, j, hj⟩ := pig b s sin
  replace hi {y} h := @hi y (t_s h)

  have ⟨u, hu, v, hv, huv⟩ := tin.nontrivial
  obtain rfl : i = j := tri huv (hi hu) (hi hv) |>.symm.trans <| tri huv (hj hu) (hj hv)
  refine hb $ tri x_b (hs .. |>.trans <| hi hu) (hs .. |>.trans <| hj hu)
