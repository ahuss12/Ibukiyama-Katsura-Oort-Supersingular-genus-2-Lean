import Lake
open Lake DSL

-- Selected upstream import closure with documented compatibility edits.
-- See upstream-manifest.json and port-manifest.json for exact provenance.
package flt_subset where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`maxHeartbeats, (4000000 : Nat)⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩,
    ⟨`backward.isDefEq.respectTransparency.types, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @
  "85e3a25e006c35636f0e53b0e9296caca2685bc0"

lean_lib P2M where
  globs := #[.submodules `P2M]

lean_lib Definitions where
  globs := #[.submodules `Definitions]

lean_lib Theorems where
  globs := #[.submodules `Theorems]
