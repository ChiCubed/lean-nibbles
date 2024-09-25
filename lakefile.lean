import Lake
open Lake DSL

package «chis-nibbles» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  moreServerOptions := #[
    -- no thanks
    ⟨`linter.style.cdot, false⟩,
    ⟨`linter.style.dollarSyntax, false⟩,
    ⟨`linter.style.lambdaSyntax, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib ChisNibbles
