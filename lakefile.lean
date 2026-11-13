import Lake
open Lake DSL

package «symplectic-pairwise-3body» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

@[default_target]
lean_lib «SymplecticThreeBody» where
  roots := #[`SymplecticThreeBody]
