import Lake
open Lake DSL

package «gromov-hyperbolicity» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, true⟩,
    ⟨`warningAsError, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ s!"v{Lean.versionString}"

lean_lib Examples

@[default_target]
lean_lib EssenLectures
