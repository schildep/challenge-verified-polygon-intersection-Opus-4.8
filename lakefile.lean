import Lake
open Lake DSL

package «Polygons2» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Polygons2» where
  globs := #[.submodules `Polygons2]
