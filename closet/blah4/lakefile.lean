import Lake
open Lake DSL

package blah4 where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- TODO figure out how to make dependencies actually work?

@[default_target]
lean_lib Blah4 where
  roots := #[`Blah4]

lean_lib Utils where
  roots := #[`Utils]
