import Mathlib

open Cardinal Ordinal



-- theorem cardinality_induction {α β}
--   (S : Set (α →. β))
--   (h_zero : default ∈ S)
--   (h_succ : ∀ f ∈ S, #f.Dom < #α →
--     ∀ x ∉ f.Dom, ∃ g ∈ S, g.Dom = f.Dom ∪ {x} ∧ ∀ i, f i ≤ g i) :
--     ∃ f : α → β, ↑f ∈ S := by
--   obtain ⟨r, wo, hr⟩ := ord_eq α
--   have e : {i | i < ord #α} ≃ α := hr.symm ▸ enumIso r |>.toEquiv
--   suffices ∃ f : α → β, ∀ i ≤ ord #α, PFun.res f (e '' {j | j < i}) ∈ S by
--     sorry

--   suffices ∀ i ≤ ord #α, ∃ f ∈ S, f.Dom = e '' {j | j < i} by
--     obtain ⟨f, hf, f_dom⟩ := this _ le_rfl
--     exists fun a => f.fn a (show a ∈ f.Dom by simpa [f_dom] using (e.symm a).2)
--     convert hf; apply PFun.ext; simp
--   intro i
--   induction i using Ordinal.limitRecOn with
--   | H₁ => exact fun _ => ⟨default, h_zero, by simp [default, Ordinal.not_lt_zero]⟩
--   | H₂ i ih =>
--     simp_rw [Order.succ_le_iff, Order.lt_succ_iff]
--     intro hi
--     rcases ih hi.le with ⟨f, hf, f_dom⟩
--     have := h_succ f hf sorry (e ⟨i, hi⟩)
