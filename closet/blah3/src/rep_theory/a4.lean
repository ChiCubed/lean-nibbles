import representation_theory.basic
import algebra.module.basic

import linear_algebra.span

-- argh this all sucks.
-- stop here for now?

namespace stuffs

section

open_locale direct_sum

-- Algebras *do* have to have additive inverses for us, right?

parameters (𝕜 : Type*) [field 𝕜]
parameters (ι : Type*) [fintype ι] [decidable_eq ι] (A : ι → Type*)
parameters [Π i, ring (A i)] [Π i, algebra 𝕜 (A i)]

-- Let's prove things in terms of the product for now,
-- since the direct sum is only unital when there are finitely many things.
-- (we have an instance for non_unital_ring on finsupp,
-- maybe finsupp is better than direct sum for now?)

abbreviation TA := ⨁ i, A i

instance baba : non_unital_ring TA :=
sorry

instance : ring TA :=


example : algebra 𝕜 TA := by apply_instance

parameters (V : Type*) [add_comm_group V] [module TA V]

def Vπ (i : ι) : submodule TA V :=
(⊤ : submodule TA V).map $
show linear_map (ring_hom.id TA) V V, from
⟨ λ (x : V), (λ j, ite (i = j) 1 0 : TA) • x,
  λ x y, smul_add _ _ _,
  λ r x, begin
    simp_rw [ring_hom.id_apply, ← mul_smul],
    congr' 1,
    ext j,
    by_cases i = j; simp [h],
  end ⟩



end

end stuffs