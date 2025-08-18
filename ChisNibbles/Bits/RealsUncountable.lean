import Mathlib

/-
An unusual proof of the uncountability of the reals,
by showing that the sum of |ℝ| positive reals is ∞.

The proof here is by considering, for a contradiction,
the supremum of {x | x ≤ ∑_{y < x} f(y)}.
-/

theorem real_induction
  (S : Set ℝ)
  (hbase : S.Nonempty)
  (hsucc : ∀ x ∈ S, ∃ y ∈ S, x < y)
  (hlim : ∀ x, IsLUB S x → x ∈ S) :
    IsCofinal S := by
  contrapose! hsucc with S_bdd
  apply BddAbove.of_not_isCofinal at S_bdd
  exact ⟨sSup S, hlim _ (isLUB_csSup hbase S_bdd), fun _ => le_csSup S_bdd⟩

open Set in
theorem real_sized_sum_lemma
  (f : ℝ → ℝ) (f_pos : ∀ x, 0 < f x) :
    ¬ Summable f := by
  intro f_sble
  have f_nn x : 0 ≤ f x := f_pos x |>.le

  let F x := Iio x |>.indicator f
  have F_nn {x} : 0 ≤ F x := indicator_nonneg fun x _ => f_nn x
  have F_mono' : Monotone F := fun ⦃x y⦄ h => indicator_le_indicator_of_subset (Iio_subset_Iio h) f_nn
  have F_le_f {x} : F x ≤ f := indicator_le_self' fun x _ => f_nn x
  have F_sble {x} : Summable (F x) := f_sble.indicator _

  suffices IsCofinal {x | x ≤ tsum (F x)} by
    have ⟨T, hT⟩ := f_sble
    have ⟨y, hy, h⟩ := this (T + 1)
    suffices T + 1 ≤ T by linarith only [this]
    calc
      T + 1 ≤ tsum (F _) := h.trans hy
      _     ≤ tsum f     := F_sble.tsum_le_tsum F_le_f f_sble
      _     = T          := hT.tsum_eq
  apply real_induction
  . exact ⟨0, tsum_nonneg F_nn⟩
  . intro x hx
    exists x + f x
    dsimp only [mem_setOf_eq] at *
    constructor
    . let g := Ico x (x + f x) |>.indicator f
      have : F (x + f x) = F x + g :=
        congr($(Iio_union_Ico_eq_Iio <| show x ≤ x + f x by linarith only [f_nn x]).indicator f).symm.trans <|
          indicator_union_of_disjoint (Iio_disjoint_Ici le_rfl |>.mono le_rfl Ico_subset_Ici_self) f
      have g_sble : Summable g := f_sble.indicator _
      erw [this, F_sble.tsum_add g_sble]
      apply add_le_add hx
      calc
        f x = g x    := symm <| indicator_of_mem (by simp [f_pos x]) f
        _   ≤ tsum g := g_sble.le_tsum x fun y _ => indicator_nonneg (fun x _ => f_nn x) y
    . simp [f_pos]
  . exact fun x hx => hx.2 <| fun v hv =>
      hv.trans <| F_sble.tsum_mono F_sble <| F_mono' <| hx.1 hv

example : Uncountable ℝ := .mk fun ⟨f, hf⟩ =>
  real_sized_sum_lemma ((1 / 2) ^ f ·) (by simp) <|
    summable_geometric_two.comp_injective hf
