import Lake
open Lake DSL

package "PBCore006" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «PBCore006» where
  roots := #[`PBCore006]
